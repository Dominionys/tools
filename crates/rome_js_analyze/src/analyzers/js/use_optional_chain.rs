use std::cmp::Ordering;
use std::collections::VecDeque;
use std::iter;

use rome_analyze::{
    context::RuleContext, declare_rule, ActionCategory, Ast, Rule, RuleCategory, RuleDiagnostic,
};
use rome_console::markup;
use rome_diagnostics::Applicability;
use rome_js_factory::make;
use rome_js_syntax::{
    JsAnyExpression, JsAnyName, JsComputedMemberExpression, JsLogicalExpression, JsLogicalOperator,
    JsStaticMemberExpression, OperatorPrecedence, T,
};
use rome_rowan::{declare_node_union, AstNode, AstNodeExt, BatchMutationExt, SyntaxResult};

use crate::JsRuleAction;

declare_rule! {
    /// Enforce using concise optional chain instead of chained logical expressions.
    ///
    /// TypeScript 3.7 added support for the optional chain operator.
    /// This operator allows you to safely access properties and methods on objects when they are potentially `null` or `undefined`.
    /// The optional chain operator only chains when the property value is `null` or `undefined`.
    /// It is much safer than relying upon logical operator chaining; which chains on any truthy value.
    ///
    /// ## Examples
    ///
    /// ### Invalid
    ///
    /// ```js,expect_diagnostic
    /// foo && foo.bar && foo.bar.baz && foo.bar.baz.buzz
    /// ```
    ///
    /// ```js,expect_diagnostic
    /// foo.bar && foo.bar.baz.buzz
    /// ```
    ///
    /// ```js,expect_diagnostic
    /// foo !== undefined && foo.bar != undefined && foo.bar.baz !== null && foo.bar.baz.buzz
    /// ```
    ///
    /// ```js,expect_diagnostic
    /// ((foo || {}).bar || {}).baz;
    /// ```
    ///
    /// ```js,expect_diagnostic
    /// (await (foo1 || {}).foo2 || {}).foo3;
    /// ```
    ///
    /// ```ts,expect_diagnostic
    /// (((typeof x) as string) || {}).bar;
    /// ```
    ///
    /// ### Valid
    ///
    /// ```js
    /// foo && bar;
    ///```
    /// ```js
    /// foo || {};
    ///```
    ///
    /// ```js
    /// (foo = 2 || {}).bar;
    ///```
    ///
    /// ```js
    /// foo || foo.bar;
    ///```
    ///
    /// ```js
    /// foo["some long"] && foo["some long string"].baz
    ///```
    ///
    pub(crate) UseOptionalChain {
        version: "0.9.0",
        name: "useOptionalChain",
        recommended: true,
    }
}

pub(crate) enum UseOptionalChainState {
    LogicalAnd(VecDeque<JsAnyExpression>),
    LogicalOrLike(LogicalOrLikeChain),
}

impl Rule for UseOptionalChain {
    const CATEGORY: RuleCategory = RuleCategory::Lint;

    type Query = Ast<JsLogicalExpression>;
    type State = UseOptionalChainState;
    type Signals = Option<Self::State>;

    fn run(ctx: &RuleContext<Self>) -> Option<Self::State> {
        let logical = ctx.query();
        let operator = logical.operator().ok()?;

        match operator {
            JsLogicalOperator::LogicalAnd => {
                let chain = LogicalAndChain::new(logical.right().ok()?);

                if chain.is_inside_another_chain().unwrap_or(false) {
                    return None;
                }

                let optional_chain_expression_nodes = chain.optional_chain_expression_nodes()?;

                if optional_chain_expression_nodes.is_empty() {
                    return None;
                }

                Some(UseOptionalChainState::LogicalAnd(
                    optional_chain_expression_nodes,
                ))
            }
            JsLogicalOperator::NullishCoalescing | JsLogicalOperator::LogicalOr => {
                let chain = LogicalOrLikeChain::new(logical)?;

                if chain.is_inside_another_chain() {
                    return None;
                }

                Some(UseOptionalChainState::LogicalOrLike(chain))
            }
        }
    }

    fn diagnostic(ctx: &RuleContext<Self>, state: &Self::State) -> Option<RuleDiagnostic> {
        let range = match state {
            UseOptionalChainState::LogicalAnd(_) => ctx.query().range(),
            UseOptionalChainState::LogicalOrLike(state) => state.member.range(),
        };

        Some(RuleDiagnostic::new(
            range,
            markup! {
                "Change to an optional chain."
            }
            .to_owned(),
        ))
    }

    fn action(ctx: &RuleContext<Self>, state: &Self::State) -> Option<JsRuleAction> {
        match state {
            UseOptionalChainState::LogicalAnd(optional_chain_expression_nodes) => {
                let mut prev_expression = None;

                for expression in optional_chain_expression_nodes {
                    let next_expression = prev_expression
                        .take()
                        .and_then(|(prev_expression, new_expression)| {
                            expression
                                .clone()
                                .replace_node(prev_expression, new_expression)
                        })
                        .unwrap_or_else(|| expression.clone());

                    let next_expression = match next_expression {
                        JsAnyExpression::JsCallExpression(call_expression) => {
                            let mut call_expression_builder = make::js_call_expression(
                                call_expression.callee().ok()?,
                                call_expression.arguments().ok()?,
                            )
                            .with_optional_chain_token(make::token(T![?.]));

                            if let Some(type_arguments) = call_expression.type_arguments() {
                                call_expression_builder =
                                    call_expression_builder.with_type_arguments(type_arguments);
                            }

                            let call_expression = call_expression_builder.build();

                            JsAnyExpression::from(call_expression)
                        }
                        JsAnyExpression::JsStaticMemberExpression(member_expression) => {
                            JsAnyExpression::from(make::js_static_member_expression(
                                member_expression.object().ok()?,
                                make::token(T![?.]),
                                member_expression.member().ok()?,
                            ))
                        }
                        JsAnyExpression::JsComputedMemberExpression(member_expression) => {
                            JsAnyExpression::from(
                                make::js_computed_member_expression(
                                    member_expression.object().ok()?,
                                    member_expression.l_brack_token().ok()?,
                                    member_expression.member().ok()?,
                                    member_expression.r_brack_token().ok()?,
                                )
                                .with_optional_chain_token(make::token(T![?.]))
                                .build(),
                            )
                        }
                        _ => return None,
                    };

                    prev_expression = Some((expression.clone(), next_expression));
                }

                let (prev_expression, new_expression) = prev_expression?;

                let logical = ctx.query();
                let next_right = logical
                    .right()
                    .ok()?
                    .replace_node(prev_expression, new_expression.clone())
                    .unwrap_or(new_expression);

                let mut mutation = ctx.root().begin();

                mutation.replace_node(JsAnyExpression::from(logical.clone()), next_right);

                Some(JsRuleAction {
                    category: ActionCategory::QuickFix,
                    applicability: Applicability::MaybeIncorrect,
                    message: markup! { "Change to an optional chain." }.to_owned(),
                    mutation,
                })
            }
            UseOptionalChainState::LogicalOrLike(chain) => {
                let chain = chain.optional_chain_expression_nodes();

                let mut prev_chain: Option<(JsAnyMemberExpression, JsAnyMemberExpression)> = None;

                for (left, member) in chain {
                    let left = if let Some((prev_member, next_member)) = prev_chain.take() {
                        left.replace_node(prev_member, next_member.clone())
                            .unwrap_or_else(|| next_member.into())
                    } else {
                        left
                    };

                    let left = trim_trailing_space(left)?;
                    let need_parenthesis =
                        left.precedence().ok()? < OperatorPrecedence::LeftHandSide;

                    let left = if need_parenthesis {
                        make::js_parenthesized_expression(
                            make::token(T!['(']),
                            left,
                            make::token(T![')']),
                        )
                        .into()
                    } else {
                        left
                    };

                    let next_member = match member.clone() {
                        JsAnyMemberExpression::JsStaticMemberExpression(expression) => {
                            let static_member_expression = make::js_static_member_expression(
                                left,
                                make::token(T![?.]),
                                expression.member().ok()?,
                            );
                            JsAnyMemberExpression::from(static_member_expression)
                        }
                        JsAnyMemberExpression::JsComputedMemberExpression(expression) => {
                            let computed_member_expression = make::js_computed_member_expression(
                                left,
                                expression.l_brack_token().ok()?,
                                expression.member().ok()?,
                                expression.r_brack_token().ok()?,
                            )
                            .with_optional_chain_token(make::token(T![?.]))
                            .build();

                            computed_member_expression.into()
                        }
                    };

                    prev_chain = Some((member, next_member));
                }

                let (prev_member, new_member) = prev_chain?;

                let mut mutation = ctx.root().begin();

                mutation.replace_node(prev_member, new_member);

                Some(JsRuleAction {
                    category: ActionCategory::QuickFix,
                    applicability: Applicability::MaybeIncorrect,
                    message: markup! { "Change to an optional chain." }.to_owned(),
                    mutation,
                })
            }
        }
    }
}

enum ChainOrdering {
    SubChain,
    Equal,
    Different,
}

/// `LogicalAndChain` handles cases with `JsLogicalExpression` which has `JsLogicalOperator::LogicalAnd` operator:
/// ```js
/// foo && foo.bar && foo.bar.baz && foo.bar.baz.buzz;
/// foo.bar && foo.bar.baz && foo.bar.baz.buzz;
/// foo !== undefined && foo.bar;
/// ```
/// The main idea of the `LogicalAndChain`:
/// 1. Check that the current chain isn't in another `LogicalAndChain`. We need to find the topmost logical expression which will be the head of the first current chain.
/// 2. Go down thought logical expressions and collect other chains and compare them with the current one.
/// 3. If a chain is a sub-chain of the current chain, we assign that sub-chain to new current one. Difference between current chain and sub-chain is a tail.
/// 4. Save the first tail `JsAnyExpression` to the buffer.
/// 5. Transform every `JsAnyExpression` from the buffer to optional expression.
///
/// E.g. `foo && foo.bar.baz && foo.bar.baz.zoo;`.
/// The logical expression `foo && foo.bar.baz` isn't the topmost. We skip it.
/// `foo && foo.bar.baz && foo.bar.baz.zoo;` is the topmost and it'll be a start point.
/// We start collecting a chain. We collect `JsAnyExpression` but for clarity let's use string identifiers.
/// `foo.bar.baz.zoo;` -> `[foo, bar, baz, zoo]`
/// Next step we take a next chain and also collect it.
/// `foo.bar.baz` -> `[foo, bar, baz]`
/// By comparing them we understand that one is a sub-chain of the other. `[foo, bar, baz]` is new current chain. `[zoo]` is a tail.
/// We save `zoo` expression to the buffer.
/// Next step we take a next chain and also collect it.
/// `foo` -> `[foo]`
/// By comparing them we understand that one is a sub-chain of the other. `[foo]` is new current chain. `[bar, baz]` is a tail.
/// We save `bar` expression to the buffer.
/// Iterate buffer `[bar, zoo]` we need to make every `JsAnyExpression` optional: `foo?.bar.baz?.zoo;`
///
#[derive(Debug)]
pub(crate) struct LogicalAndChain {
    head: JsAnyExpression,
    buf: VecDeque<JsAnyExpression>,
}

impl LogicalAndChain {
    fn new(head: JsAnyExpression) -> LogicalAndChain {
        fn collect_chain(expression: JsAnyExpression) -> VecDeque<JsAnyExpression> {
            let mut buf = VecDeque::new();

            let mut current_expression = Some(expression);

            while let Some(expression) = current_expression.take() {
                let expression = match expression {
                    JsAnyExpression::JsBinaryExpression(expression) => {
                        if expression.is_optional_chain_like().unwrap_or(false) {
                            match expression.left() {
                                Ok(left) => left,
                                Err(_) => return buf,
                            }
                        } else {
                            return buf;
                        }
                    }
                    expression => expression,
                };

                match &expression {
                    JsAnyExpression::JsStaticMemberExpression(member_expression) => {
                        current_expression = member_expression.object().ok();

                        buf.push_front(expression);
                    }
                    JsAnyExpression::JsComputedMemberExpression(member_expression) => {
                        current_expression = member_expression.object().ok();

                        buf.push_front(expression);
                    }
                    JsAnyExpression::JsIdentifierExpression(_) => {
                        buf.push_front(expression);
                    }
                    JsAnyExpression::JsCallExpression(call_expression) => {
                        current_expression = call_expression.callee().ok();

                        buf.push_front(expression);
                    }
                    _ => return buf,
                }
            }

            buf
        }

        let buf = collect_chain(head.clone());

        LogicalAndChain { head, buf }
    }

    fn is_inside_another_chain(&self) -> SyntaxResult<bool> {
        if let Some(parent) = self.head.parent::<JsLogicalExpression>() {
            if let Some(grand_parent) = parent.parent::<JsLogicalExpression>() {
                let operator = grand_parent.operator()?;

                if !matches!(operator, JsLogicalOperator::LogicalAnd) {
                    return Ok(false);
                }

                let grand_parent_logical_left = grand_parent.left()?;

                if grand_parent_logical_left.as_js_logical_expression() == Some(&parent) {
                    let grand_parent_right_chain = LogicalAndChain::new(grand_parent.right()?);

                    let result = grand_parent_right_chain.cmp_chain(self)?;

                    return match result {
                        ChainOrdering::SubChain | ChainOrdering::Equal => Ok(true),
                        ChainOrdering::Different => Ok(false),
                    };
                }
            }
        }
        Ok(false)
    }

    fn cmp_chain(&self, other: &LogicalAndChain) -> SyntaxResult<ChainOrdering> {
        let chain_ordering = match self.buf.len().cmp(&other.buf.len()) {
            Ordering::Less => return Ok(ChainOrdering::Different),
            Ordering::Equal => ChainOrdering::Equal,
            Ordering::Greater => ChainOrdering::SubChain,
        };

        for (main_expression, branch_expression) in self.buf.iter().zip(&other.buf) {
            let (main_expression, branch_expression) = match (&main_expression, &branch_expression)
            {
                (
                    JsAnyExpression::JsCallExpression(main_expression),
                    JsAnyExpression::JsCallExpression(branch_expression),
                ) => (main_expression.callee()?, branch_expression.callee()?),
                _ => (main_expression.clone(), branch_expression.clone()), //TODO maybe COW?
            };

            let (main_value_token, branch_value_token) = match (main_expression, branch_expression)
            {
                (
                    JsAnyExpression::JsComputedMemberExpression(main_expression),
                    JsAnyExpression::JsComputedMemberExpression(branch_expression),
                ) => match (main_expression.member()?, branch_expression.member()?) {
                    (
                        JsAnyExpression::JsIdentifierExpression(main_identifier),
                        JsAnyExpression::JsIdentifierExpression(branch_identifier),
                    ) => (
                        main_identifier.name()?.value_token()?,
                        branch_identifier.name()?.value_token()?,
                    ),
                    (
                        JsAnyExpression::JsAnyLiteralExpression(main_expression),
                        JsAnyExpression::JsAnyLiteralExpression(branch_expression),
                    ) => (
                        main_expression.value_token()?,
                        branch_expression.value_token()?,
                    ),
                    _ => return Ok(ChainOrdering::Different),
                },
                (
                    JsAnyExpression::JsStaticMemberExpression(main_expression),
                    JsAnyExpression::JsStaticMemberExpression(branch_expression),
                ) => match (main_expression.member()?, branch_expression.member()?) {
                    (JsAnyName::JsName(main_name), JsAnyName::JsName(branch_name)) => {
                        (main_name.value_token()?, branch_name.value_token()?)
                    }
                    (
                        JsAnyName::JsPrivateName(main_name),
                        JsAnyName::JsPrivateName(branch_name),
                    ) => (main_name.value_token()?, branch_name.value_token()?),
                    _ => return Ok(ChainOrdering::Different),
                },
                (
                    JsAnyExpression::JsIdentifierExpression(main_expression),
                    JsAnyExpression::JsIdentifierExpression(branch_expression),
                ) => (
                    main_expression.name()?.value_token()?,
                    branch_expression.name()?.value_token()?,
                ),
                _ => return Ok(ChainOrdering::Different),
            };

            if main_value_token.token_text_trimmed() != branch_value_token.token_text_trimmed() {
                return Ok(ChainOrdering::Different);
            }
        }

        Ok(chain_ordering)
    }

    fn optional_chain_expression_nodes(mut self) -> Option<VecDeque<JsAnyExpression>> {
        let mut optional_chain_expression_nodes = VecDeque::with_capacity(self.buf.len());

        let mut next_chain_head = self.head.parent::<JsLogicalExpression>()?.left().ok();

        while let Some(expression) = next_chain_head.take() {
            let expression = match expression {
                JsAnyExpression::JsBinaryExpression(expression) => expression
                    .is_optional_chain_like()
                    .ok()?
                    .then_some(expression.left().ok()?)?,
                expression => expression,
            };

            let head = match expression {
                JsAnyExpression::JsLogicalExpression(logical) => {
                    if matches!(logical.operator().ok()?, JsLogicalOperator::LogicalAnd) {
                        next_chain_head = logical.left().ok();

                        logical.right().ok()?
                    } else {
                        return None;
                    }
                }
                JsAnyExpression::JsIdentifierExpression(_)
                | JsAnyExpression::JsStaticMemberExpression(_)
                | JsAnyExpression::JsComputedMemberExpression(_)
                | JsAnyExpression::JsCallExpression(_) => expression,
                _ => return None,
            };

            let branch = LogicalAndChain::new(head);

            match self.cmp_chain(&branch).ok()? {
                ChainOrdering::SubChain => {
                    let mut tail = self.buf.split_off(branch.buf.len());

                    if let Some(part) = tail.pop_front() {
                        optional_chain_expression_nodes.push_front(part)
                    };
                }
                ChainOrdering::Equal => continue,
                ChainOrdering::Different => return None,
            }
        }

        Some(optional_chain_expression_nodes)
    }
}

/// `LogicalOrLikeChain` handles cases with `JsLogicalExpression` which has `JsLogicalOperator::NullishCoalescing` or `JsLogicalOperator::LogicalOr` operator:
/// ```js
/// (foo || {}).bar;
/// (foo ?? {}).bar;
/// ((foo ?? {}).bar || {}).baz;
/// ```
/// The main idea of the `LogicalOrLikeChain`:
/// 1. Check that the current member expressions isn't in another `LogicalOrLikeChain`. We need to find the topmost member expression.
/// 2. Go down thought logical expressions and collect left and member expressions to buffer.
/// 3. Transform every left `JsAnyExpression` and member `JsAnyMemberExpression` expressions into optional `JsAnyMemberExpression`.
///
/// E.g. `((foo ?? {}).bar || {}).baz;`.
/// The member expression `(foo ?? {}).bar` isn't the topmost. We skip it.
/// `((foo ?? {}).bar || {}).baz;` is the topmost and it'll be a start point.
/// We start collecting a left and member expressions to buffer.
/// First expression is `((foo ?? {}).bar || {}).baz;`:
/// Buffer is `[((foo ?? {}).bar, ((foo ?? {}).bar || {}).baz;)]`
/// Next expressions is `((foo ?? {}).bar || {}).baz;`:
/// Buffer is `[(foo, (foo ?? {}).bar), ((foo ?? {}).bar, ((foo ?? {}).bar || {}).baz;)]`
/// Iterate buffer, take member expressions and replace object with left parts:
/// `foo?.bar?.baz;`
///
#[derive(Debug)]
pub(crate) struct LogicalOrLikeChain {
    member: JsAnyMemberExpression,
}

impl LogicalOrLikeChain {
    fn new(logical: &JsLogicalExpression) -> Option<LogicalOrLikeChain> {
        let is_right_empty_object = logical
            .right()
            .ok()?
            .omit_parentheses()
            .as_js_object_expression()?
            .is_empty();

        if !is_right_empty_object {
            return None;
        }

        let parent = LogicalOrLikeChain::get_chain_parent(JsAnyExpression::from(logical.clone()))?;

        let member = match parent {
            JsAnyExpression::JsComputedMemberExpression(expression) => {
                JsAnyMemberExpression::from(expression)
            }
            JsAnyExpression::JsStaticMemberExpression(expression) => {
                JsAnyMemberExpression::from(expression)
            }
            _ => return None,
        };

        Some(LogicalOrLikeChain { member })
    }

    fn is_inside_another_chain(&self) -> bool {
        LogicalOrLikeChain::get_chain_parent(JsAnyExpression::from(self.member.clone())).map_or(
            false,
            |parent| {
                parent
                    .as_js_logical_expression()
                    .filter(|parent_expression| {
                        matches!(
                            parent_expression.operator(),
                            Ok(JsLogicalOperator::NullishCoalescing | JsLogicalOperator::LogicalOr)
                        )
                    })
                    .and_then(LogicalOrLikeChain::new)
                    .is_some()
            },
        )
    }

    fn optional_chain_expression_nodes(
        &self,
    ) -> VecDeque<(JsAnyExpression, JsAnyMemberExpression)> {
        let mut chain = VecDeque::new();

        let mut member = Some(self.member.clone());

        while let Some(current_member) = member.take() {
            let object = match current_member.object() {
                Ok(object) => object,
                _ => return chain,
            };

            if let JsAnyExpression::JsLogicalExpression(logical) = object.omit_parentheses() {
                let is_valid_operator = logical.operator().map_or(false, |operator| {
                    matches!(
                        operator,
                        JsLogicalOperator::NullishCoalescing | JsLogicalOperator::LogicalOr
                    )
                });

                if !is_valid_operator {
                    return chain;
                }

                let is_right_empty_object = logical
                    .right()
                    .ok()
                    .and_then(|right| {
                        right
                            .omit_parentheses()
                            .as_js_object_expression()
                            .map(|object| object.is_empty())
                    })
                    .unwrap_or(false);

                if !is_right_empty_object {
                    return chain;
                }

                let left = match logical.left() {
                    Ok(left) => left,
                    Err(_) => return chain,
                };

                member = LogicalOrLikeChain::get_member(left.clone());

                chain.push_front((left, current_member))
            }
        }

        chain
    }

    fn get_chain_parent(expression: JsAnyExpression) -> Option<JsAnyExpression> {
        iter::successors(expression.parent::<JsAnyExpression>(), |expression| {
            if matches!(
                expression,
                JsAnyExpression::JsParenthesizedExpression(_)
                    | JsAnyExpression::JsAwaitExpression(_)
                    | JsAnyExpression::JsCallExpression(_)
                    | JsAnyExpression::JsNewExpression(_)
                    | JsAnyExpression::TsAsExpression(_)
                    | JsAnyExpression::TsNonNullAssertionExpression(_)
                    | JsAnyExpression::TsTypeAssertionExpression(_)
            ) {
                expression.parent::<JsAnyExpression>()
            } else {
                None
            }
        })
        .last()
    }

    fn get_member(expression: JsAnyExpression) -> Option<JsAnyMemberExpression> {
        let expression = iter::successors(Some(expression), |expression| match expression {
            JsAnyExpression::JsParenthesizedExpression(expression) => expression.expression().ok(),
            JsAnyExpression::JsAwaitExpression(expression) => expression.argument().ok(),
            JsAnyExpression::JsCallExpression(expression) => expression.callee().ok(),
            JsAnyExpression::JsNewExpression(expression) => expression.callee().ok(),
            JsAnyExpression::TsAsExpression(expression) => expression.expression().ok(),
            JsAnyExpression::TsNonNullAssertionExpression(expression) => {
                expression.expression().ok()
            }
            JsAnyExpression::TsTypeAssertionExpression(expression) => expression.expression().ok(),
            _ => None,
        })
        .last()?;

        let expression = match expression {
            JsAnyExpression::JsComputedMemberExpression(expression) => {
                JsAnyMemberExpression::from(expression)
            }
            JsAnyExpression::JsStaticMemberExpression(expression) => {
                JsAnyMemberExpression::from(expression)
            }
            _ => return None,
        };

        Some(expression)
    }
}

fn trim_trailing_space(node: JsAnyExpression) -> Option<JsAnyExpression> {
    if let Some(last_token_of_left_syntax) = node.syntax().last_token() {
        let next_token_of_left_syntax = last_token_of_left_syntax
            .clone()
            .with_trailing_trivia(std::iter::empty());
        node.replace_token_discard_trivia(last_token_of_left_syntax, next_token_of_left_syntax)
    } else {
        Some(node)
    }
}

declare_node_union! {
    pub (crate) JsAnyMemberExpression = JsComputedMemberExpression | JsStaticMemberExpression
}

impl From<JsAnyMemberExpression> for JsAnyExpression {
    fn from(expression: JsAnyMemberExpression) -> Self {
        match expression {
            JsAnyMemberExpression::JsComputedMemberExpression(expression) => expression.into(),
            JsAnyMemberExpression::JsStaticMemberExpression(expression) => expression.into(),
        }
    }
}

impl JsAnyMemberExpression {
    fn object(&self) -> SyntaxResult<JsAnyExpression> {
        match self {
            JsAnyMemberExpression::JsComputedMemberExpression(expression) => expression.object(),
            JsAnyMemberExpression::JsStaticMemberExpression(expression) => expression.object(),
        }
    }
}
