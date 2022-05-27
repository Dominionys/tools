pub(crate) mod array;
mod binary_like_expression;
mod format_conditional;
mod simple;
pub mod string_utils;

mod member_chain;
#[cfg(test)]
mod quickcheck_utils;

use crate::prelude::*;
pub(crate) use binary_like_expression::{format_binary_like_expression, JsAnyBinaryLikeExpression};
pub(crate) use format_conditional::{format_conditional, Conditional};
pub(crate) use member_chain::format_call_expression;
use rome_formatter::normalize_newlines;
use rome_js_syntax::suppression::{has_suppressions_category, SuppressionCategory};
use rome_js_syntax::{
    JsAnyExpression, JsAnyFunction, JsAnyStatement, JsInitializerClause, JsLanguage,
    JsTemplateElement, JsTemplateElementFields, Modifiers, TsTemplateElement,
    TsTemplateElementFields, TsType,
};
use rome_js_syntax::{JsSyntaxKind, JsSyntaxNode, JsSyntaxToken};
use rome_rowan::{AstNode, AstNodeList};
use std::borrow::Cow;

use crate::options::{JsFormatOptions, QuoteStyle};
pub(crate) use simple::*;

/// Utility function to format the separators of the nodes that belong to the unions
/// of [rome_js_syntax::TsAnyTypeMember].
///
/// We can have two kind of separators: `,`, `;` or ASI.
/// Because of how the grammar crafts the nodes, the parent will add the separator to the node.
/// So here, we create - on purpose - an empty node.
pub(crate) fn format_type_member_separator(
    separator_token: Option<JsSyntaxToken>,
    formatter: &Formatter<JsFormatOptions>,
) -> FormatElement {
    if let Some(separator) = separator_token {
        formatter.format_replaced(&separator, empty_element())
    } else {
        empty_element()
    }
}

/// Utility function to format the node [rome_js_syntax::JsInitializerClause]
pub(crate) fn format_initializer_clause(
    formatter: &Formatter<JsFormatOptions>,
    initializer: Option<JsInitializerClause>,
) -> FormatResult<FormatElement> {
    formatted![
        formatter,
        [initializer
            .format()
            .with_or_empty(|initializer| { formatted![formatter, [space_token(), initializer]] })]
    ]
}

pub(crate) fn format_interpreter(
    interpreter: Option<JsSyntaxToken>,
    formatter: &Formatter<JsFormatOptions>,
) -> FormatResult<FormatElement> {
    formatted![
        formatter,
        [interpreter.format().with_or(
            |interpreter| formatted![formatter, [interpreter, empty_line()]],
            empty_element,
        )]
    ]
}

/// Returns true if this node contains "printable" trivias: comments
/// or empty lines (2 consecutive newlines only separated by whitespace)
pub(crate) fn has_formatter_trivia(node: &JsSyntaxNode) -> bool {
    let mut line_count = 0;

    for token in node.descendants_tokens() {
        for trivia in token.leading_trivia().pieces() {
            if trivia.is_comments() {
                return true;
            } else if trivia.is_newline() {
                line_count += 1;
                if line_count >= 2 {
                    return true;
                }
            }
        }

        // This is where the token would be,
        // reset the consecutive newline counter
        line_count = 0;

        for trivia in token.trailing_trivia().pieces() {
            if trivia.is_comments() {
                return true;
            } else if trivia.is_newline() {
                line_count += 1;
                if line_count >= 2 {
                    return true;
                }
            }
        }
    }

    false
}

/// Returns true if this node contains newlines in trivias.
pub(crate) fn has_leading_newline(node: &JsSyntaxNode) -> bool {
    if let Some(leading_trivia) = node.first_leading_trivia() {
        for piece in leading_trivia.pieces() {
            if piece.is_newline() {
                return true;
            }
        }
    }
    false
}

/// Format an element with a single line head and a body that might
/// be either a block or a single statement
///
/// This will place the head element inside a [hard_group_elements], but
/// the body will broken out of flat printing if its a single statement
pub(crate) fn format_head_body_statement(
    formatter: &Formatter<JsFormatOptions>,
    head: FormatElement,
    body: JsAnyStatement,
) -> FormatResult<FormatElement> {
    if matches!(body, JsAnyStatement::JsBlockStatement(_)) {
        formatted![formatter, [head, space_token(), body.format(),]]
    } else if matches!(body, JsAnyStatement::JsEmptyStatement(_)) {
        // Force semicolon insertion if the body is empty
        formatted![formatter, [head, body.format(), token(";"),]]
    } else {
        formatted![formatter, [head, space_token(), body.format(),]]
    }
}

pub(crate) fn has_formatter_suppressions(node: &JsSyntaxNode) -> bool {
    has_suppressions_category(SuppressionCategory::Format, node)
}

/// This function consumes a list of modifiers and applies a predictable sorting.
pub(crate) fn sort_modifiers_by_precedence<List, Node>(list: &List) -> Vec<Node>
where
    Node: AstNode<Language = JsLanguage>,
    List: AstNodeList<Language = JsLanguage, Node = Node>,
    Modifiers: for<'a> From<&'a Node>,
{
    let mut nodes_and_modifiers = list.iter().collect::<Vec<Node>>();

    nodes_and_modifiers.sort_unstable_by_key(|node| Modifiers::from(node));

    nodes_and_modifiers
}

/// Utility to format
pub(crate) fn format_template_chunk(
    chunk: JsSyntaxToken,
    formatter: &Formatter<JsFormatOptions>,
) -> FormatResult<FormatElement> {
    // Per https://tc39.es/ecma262/multipage/ecmascript-language-lexical-grammar.html#sec-static-semantics-trv:
    // In template literals, the '\r' and '\r\n' line terminators are normalized to '\n'
    Ok(formatter.format_replaced(
        &chunk,
        FormatElement::from(Token::from_syntax_token_cow_slice(
            normalize_newlines(chunk.text_trimmed(), ['\r']),
            &chunk,
            chunk.text_trimmed_range().start(),
        )),
    ))
}

/// Function to format template literals and template literal types
pub(crate) fn format_template_literal(
    literal: TemplateElement,
    formatter: &Formatter<JsFormatOptions>,
) -> FormatResult<FormatElement> {
    literal.into_format_element(formatter)
}

pub(crate) enum TemplateElement {
    Js(JsTemplateElement),
    Ts(TsTemplateElement),
}

impl TemplateElement {
    pub fn into_format_element(
        self,
        formatter: &Formatter<JsFormatOptions>,
    ) -> FormatResult<FormatElement> {
        let expression_is_plain = self.is_plain_expression()?;
        let has_comments = self.has_comments();
        let should_hard_group = expression_is_plain && !has_comments;

        let (dollar_curly_token, middle, r_curly_token) = match self {
            TemplateElement::Js(template_element) => {
                let JsTemplateElementFields {
                    dollar_curly_token,
                    expression,
                    r_curly_token,
                } = template_element.as_fields();

                let dollar_curly_token = dollar_curly_token?;
                let expression = formatted![formatter, [expression.format()]]?;
                let r_curly_token = r_curly_token?;

                (dollar_curly_token, expression, r_curly_token)
            }
            TemplateElement::Ts(template_element) => {
                let TsTemplateElementFields {
                    ty,
                    r_curly_token,
                    dollar_curly_token,
                } = template_element.as_fields();

                let dollar_curly_token = dollar_curly_token?;
                let ty = formatted![formatter, [ty.format()]]?;
                let r_curly_token = r_curly_token?;

                (dollar_curly_token, ty, r_curly_token)
            }
        };

        let middle = format_elements![middle, line_suffix_boundary()];

        if should_hard_group {
            formatted![
                formatter,
                [dollar_curly_token.format(), middle, r_curly_token.format()]
            ]
        } else {
            formatter
                .delimited(&dollar_curly_token, middle, &r_curly_token)
                .soft_block_indent()
                .finish()
        }
    }

    /// We want to break the template element only when we have articulated expressions inside it.
    ///
    /// We a plain expression is when it's one of the following:
    /// - `loreum ${this.something} ipsum`
    /// - `loreum ${a.b.c} ipsum`
    /// - `loreum ${a} ipsum`
    fn is_plain_expression(&self) -> FormatResult<bool> {
        match self {
            TemplateElement::Js(template_element) => {
                let current_expression = template_element.expression()?;
                match current_expression {
                    JsAnyExpression::JsStaticMemberExpression(_)
                    | JsAnyExpression::JsComputedMemberExpression(_)
                    | JsAnyExpression::JsIdentifierExpression(_)
                    | JsAnyExpression::JsAnyLiteralExpression(_)
                    | JsAnyExpression::JsCallExpression(_) => Ok(true),

                    JsAnyExpression::JsParenthesizedExpression(expression) => {
                        // binary and logical expression have their own grouping inside parenthesis,
                        // so we mark the current parenthesized expression as not plain
                        match expression.expression()? {
                            JsAnyExpression::JsLogicalExpression(_)
                            | JsAnyExpression::JsBinaryExpression(_) => Ok(false),
                            _ => Ok(true),
                        }
                    }

                    _ => {
                        if let Some(function) =
                            JsAnyFunction::cast(current_expression.syntax().clone())
                        {
                            Ok(is_simple_function_expression(function)?)
                        } else {
                            Ok(false)
                        }
                    }
                }
            }
            TemplateElement::Ts(template_element) => {
                let is_mapped_type = matches!(template_element.ty()?, TsType::TsMappedType(_));
                Ok(!is_mapped_type)
            }
        }
    }

    fn has_comments(&self) -> bool {
        match self {
            TemplateElement::Js(template_element) => {
                template_element.syntax().has_comments_descendants()
            }
            TemplateElement::Ts(template_element) => {
                template_element.syntax().has_comments_descendants()
            }
        }
    }
}

/// This enum is used to extract a precedence from certain nodes. By comparing the precedence
/// of two nodes, it's possible to change the way certain node should be formatted.
///
/// A use case, for example, is when comparing a node with its parent. If the parent has a lower
/// precedence, then the node can change its formatting.
#[derive(Debug, Ord, PartialOrd, Eq, PartialEq)]
pub(crate) enum FormatPrecedence {
    /// No precedence given to these nodes
    None,

    /// Low priority
    Low,

    /// High priority
    High,
}

impl FormatPrecedence {
    /// Use this function when you want to extract the precedence of the current node
    /// based on whether it can parenthesised or not.
    ///
    /// This function is useful when we want to compare a node against its parent. If the parent has
    /// lower precedence, it means that we can remove the parenthesis from the current node.
    ///
    /// An example can be:
    ///
    /// ```js
    /// let a = ("simple expression") + " or not";
    /// ```
    ///
    /// In this case, we have a parenthesised expression and its parent is a binary expression.
    /// The first one will have [FormatPrecedence::Low] as priority and the second has
    /// [FormatPrecedence::None] as priority. In this case, the parenthesis can be omitted.
    pub fn with_precedence_for_parenthesis(node: Option<&JsSyntaxNode>) -> Self {
        node.map_or(FormatPrecedence::None, |node| match node.kind() {
            JsSyntaxKind::JS_PARENTHESIZED_EXPRESSION => FormatPrecedence::Low,

            JsSyntaxKind::TS_AS_EXPRESSION
            | JsSyntaxKind::TS_NON_NULL_ASSERTION_EXPRESSION
            | JsSyntaxKind::TS_TYPE_ASSERTION_EXPRESSION
            | JsSyntaxKind::JS_UNARY_EXPRESSION
            | JsSyntaxKind::JS_LOGICAL_EXPRESSION
            | JsSyntaxKind::JS_BINARY_EXPRESSION
            | JsSyntaxKind::JS_TEMPLATE
            | JsSyntaxKind::JS_SPREAD
            | JsSyntaxKind::JS_STATIC_MEMBER_EXPRESSION
            | JsSyntaxKind::JS_STATIC_MEMBER_ASSIGNMENT
            | JsSyntaxKind::JS_CALL_EXPRESSION
            | JsSyntaxKind::JS_NEW_EXPRESSION
            | JsSyntaxKind::JS_CONDITIONAL_EXPRESSION
            | JsSyntaxKind::JS_EXTENDS_CLAUSE
            | JsSyntaxKind::TS_IMPLEMENTS_CLAUSE
            | JsSyntaxKind::JS_AWAIT_EXPRESSION
            | JsSyntaxKind::JS_YIELD_ARGUMENT
            | JsSyntaxKind::JS_ARROW_FUNCTION_EXPRESSION
            | JsSyntaxKind::JS_EXPRESSION_STATEMENT
            | JsSyntaxKind::JS_RETURN_STATEMENT
            | JsSyntaxKind::JS_COMPUTED_MEMBER_EXPRESSION
            | JsSyntaxKind::JS_COMPUTED_MEMBER_ASSIGNMENT => FormatPrecedence::High,

            _ => FormatPrecedence::None,
        })
    }
}

/// Format a some code followed by an optional semicolon, and performs
/// semicolon insertion if it was missing in the input source and the
/// preceeding element wasn't an unknown node
pub(crate) fn format_with_semicolon(
    formatter: &Formatter<JsFormatOptions>,
    content: FormatElement,
    semicolon: Option<JsSyntaxToken>,
) -> FormatResult<FormatElement> {
    let is_unknown = match content.last_element() {
        Some(FormatElement::Verbatim(elem)) => elem.is_unknown(),
        _ => false,
    };

    formatted![
        formatter,
        [
            content,
            semicolon.format().or_format(if is_unknown {
                empty_element
            } else {
                || token(";")
            })
        ]
    ]
}

/// This function determines which quotes should be used inside to enclose the string.
/// The function take as a input the string **without quotes**.
///
/// # Returns
///
/// A tuple where the first quote is the preferred one, the second is the alternate (the other one).
/// The first quote should be use to enclose the content of the string.
///
/// # How it works
///
/// The function determines the preferred quote and alternate quote.
/// The preferred quote is the one that comes from the formatter options. The alternate quote is the other one.
///
/// We check how many preferred quotes we have inside the content. If this number is greater then the
/// number alternate quotes that we have inside the content,
/// then we swap them, so we can reduce the number of escaped quotes.
///
/// For example, let's suppose that the preferred quote is double, and we have a string like this:
/// ```js
/// (" content \"\"\" don't ")
/// ```
/// Excluding the quotes at the start and beginning, we have three double quote and one single quote.
/// If we decided to keep them like this, we would have three escaped quotes.
///
/// But then, we choose the single quote as preferred quote and we would have only one quote that is escaped,
/// resulting into a string like this:
/// ```js
/// (' content """ dont\'t ')
/// ```
/// Like this, we reduced the number of escaped quotes.
fn computed_preferred_quote_style(
    quoteless_content: &str,
    chosen_quote_style: QuoteStyle,
) -> QuoteStyle {
    let preferred = chosen_quote_style;
    let alternate = chosen_quote_style.other();

    let (preferred_quotes_count, alternate_quotes_count) = quoteless_content.chars().fold(
        (0, 0),
        |(preferred_quotes_counter, alternate_quotes_counter), current_character| {
            if current_character == preferred.as_char() {
                (preferred_quotes_counter + 1, alternate_quotes_counter)
            } else if current_character == alternate.as_char() {
                (preferred_quotes_counter, alternate_quotes_counter + 1)
            } else {
                (preferred_quotes_counter, alternate_quotes_counter)
            }
        },
    );

    if preferred_quotes_count > alternate_quotes_count {
        return alternate;
    }

    preferred
}

/// This signal is used to tell to the next character what it should do
enum CharSignal {
    /// There hasn't been any signal
    Idle,
    /// The function decided to keep the previous character
    Keep,
    /// The function has decided to print the character
    AlreadyPrinted,
}

const CHARACTERS_THAT_COULD_KEEP_THE_ESCAPE: [char; 3] = ['\\', '\'', '"'];

/// This function is responsible to reduce the number of escaped characters inside a string
///
/// The way it works is the following: we split the content by analyzing all the
/// characters that are contained inside [CHARACTERS_THAT_COULD_KEEP_THE_ESCAPE].
///
/// Each time we retrieve one of this character, we push inside a new string all the content
/// found **before** the current character.
///
/// After that the function checks if the current character should be also be printed or not.
/// These characters (like quotes) can have an escape that might be removed. If that happens,
/// we use [CharSignal] to tell to the next iteration what it should do with that character.
///
/// For example, let's take this example:
/// ```js
/// ("hello! \'")
/// ```
///
/// Here, we want to remove the backslash (\) from the content. So when we encounter `\`,
/// the algorithm checks if after `\` there's a `'`, and if so, then we push inside the final string
/// only `'` and we ignore the backlash. Then we signal the next iteration with [CharSignal::AlreadyPrinted],
/// so when we process the next `'`, we decide to ignore it and reset the signal.
///
/// Another example is the following:
///
/// ```js
/// (" \\' ")
/// ```
///
/// Here, we need to keep all the backslash. We check the first one and we look ahead. We find another
/// `\`, so we keep it the first and we signal the next iteration with [CharSignal::Keep].
/// Then the next iteration comes along. We have the second `\`, we look ahead we find a `'`. Although,
/// as opposed to the previous example, we have a signal that says that we should keep the current
/// character. Then we do so. The third iteration comes along and we find `'`. We still have the
/// [CharSignal::Keep]. We do so and then we set the signal to [CharSignal::Idle]
///
fn reduce_escapes_from_string(
    raw_content: &str,
    preferred_quote: QuoteStyle,
    alternate_quote: QuoteStyle,
) -> Cow<str> {
    let mut reduced_string = String::new();
    let mut last_end = 0;
    let mut signal = CharSignal::Idle;

    for (start, part) in raw_content.match_indices(CHARACTERS_THAT_COULD_KEEP_THE_ESCAPE) {
        if start - last_end >= 1 {
            // This is the case where we don't have consecutive characters and if so, we have to reset the signal.
            // An example is the following: " \\u2028 ' "
            // After the two backslash, we have a character that is not a quote. So we reset the signal and we
            // iterate over the single quote, we don't deal with any edge case.
            signal = CharSignal::Idle;
        }
        reduced_string.push_str(&raw_content[last_end..start]);
        last_end = start + part.len();

        // If we encounter a preferred quote and it's not escaped, we have to replace it with
        // an escaped version.
        // This is done because of how the enclosed strings can change.
        // Check `computed_preferred_quote_style` for more details.
        if part == preferred_quote.as_string() {
            let last_char = &reduced_string.chars().last();
            if let Some('\\') = last_char {
                reduced_string.push(preferred_quote.as_char());
            } else {
                reduced_string.push_str(preferred_quote.as_escaped());
            }
        } else if part == alternate_quote.as_string() {
            match signal {
                CharSignal::Idle => {
                    reduced_string.push(alternate_quote.as_char());
                }
                CharSignal::Keep => {
                    reduced_string.push(alternate_quote.as_char());
                    signal = CharSignal::Idle;
                }
                CharSignal::AlreadyPrinted => {
                    signal = CharSignal::Idle;
                    continue;
                }
            }
        } else if part == "\\" {
            let bytes = raw_content.as_bytes();

            match bytes[start] {
                // TODO: #2444 add checks to additional characters to reduce the number of escapes
                // "\a" VS "\n" => "a" VS "\n"
                b'\\' => {
                    if start + 1 < bytes.len() {
                        // If we encounter an alternate quote that is escaped, we have to
                        // remove the escape from it.
                        // This is done because of how the enclosed strings can change.
                        // Check `computed_preferred_quote_style` for more details.
                        if bytes[start + 1] == alternate_quote.as_bytes()
                            // This check is a safety net for cases where the backslash is at the end
                            // of the raw content:
                            // ("\\")
                            // The second backslash is at the end.
                            && start + 2 <= bytes.len()
                        {
                            match signal {
                                CharSignal::Keep => {
                                    reduced_string.push('\\');
                                }
                                _ => {
                                    reduced_string.push(alternate_quote.as_char());
                                    signal = CharSignal::AlreadyPrinted;
                                }
                            }
                        } else {
                            // The next character is another backslash, let's signal
                            // the next iteration that it should keep it in the final string
                            if bytes[start + 1] == b'\\' {
                                signal = CharSignal::Keep;
                            }
                            // fallback, keep the backslash
                            reduced_string.push('\\');
                        }
                    } else {
                        // fallback, keep the backslash
                        reduced_string.push('\\');
                    }
                }
                _ => unreachable!("We checked already the presence of a backslash"),
            }
        }
    }

    // Don't allocate a new string of this is empty
    if reduced_string.is_empty() {
        Cow::Borrowed(raw_content)
    } else {
        reduced_string.push_str(&raw_content[last_end..raw_content.len()]);
        Cow::Owned(reduced_string)
    }
}

pub(crate) enum FormatLiteralStringToken<'token> {
    String(&'token JsSyntaxToken),
    Directive(&'token JsSyntaxToken),
}

impl<'token> FormatLiteralStringToken<'token> {
    pub fn from_directive(token: &'token JsSyntaxToken) -> Self {
        Self::Directive(token)
    }
    pub fn from_string(token: &'token JsSyntaxToken) -> Self {
        Self::String(token)
    }
    pub fn token(&self) -> &'token JsSyntaxToken {
        match self {
            FormatLiteralStringToken::String(token) => token,
            FormatLiteralStringToken::Directive(token) => token,
        }
    }
}

const POSSIBLE_QUOTES: [char; 2] = ['\'', '"'];

fn swap_quotes<'a, S: Into<&'a str>>(
    chosen_quote_style: QuoteStyle,
    original_content: &str,
    new_raw_content: S,
) -> Cow<str> {
    if original_content.starts_with(chosen_quote_style.other().as_char()) {
        Cow::Owned(format!(
            "{}{}{}",
            chosen_quote_style.as_char(),
            new_raw_content.into(),
            chosen_quote_style.as_char()
        ))
    } else {
        Cow::Borrowed(original_content)
    }
}

impl Format for FormatLiteralStringToken<'_> {
    type Options = JsFormatOptions;

    fn format(&self, formatter: &Formatter<Self::Options>) -> FormatResult<FormatElement> {
        let chosen_quote_style = formatter.options().quote_style;
        let token = self.token();
        let literal = token.text_trimmed();

        let content = match self {
            FormatLiteralStringToken::Directive(_) => {
                let raw_content = &literal[1..literal.len() - 1];

                if raw_content.contains(['"', '\'']) {
                    normalize_newlines(literal, ['\r'])
                } else {
                    let content = swap_quotes(chosen_quote_style, literal, raw_content);
                    match content {
                        Cow::Borrowed(content) => normalize_newlines(content, ['\r']),
                        Cow::Owned(content) => {
                            Cow::Owned(normalize_newlines(&content, ['\r']).into_owned())
                        }
                    }
                }
            }
            FormatLiteralStringToken::String(_) => {
                // literal, in our syntax, might not have quotes so we need to check if they start with a possible quote
                // is so, they are eligible for possible string manipulation
                if literal.starts_with(POSSIBLE_QUOTES) {
                    // raw_content is the content of a string without the quotes
                    let raw_content = &literal[1..literal.len() - 1];

                    let preferred_quote =
                        computed_preferred_quote_style(raw_content, chosen_quote_style);

                    let polished_raw_content = reduce_escapes_from_string(
                        raw_content,
                        preferred_quote,
                        preferred_quote.other(),
                    );

                    match polished_raw_content {
                        Cow::Borrowed(raw_content) => {
                            let final_content = swap_quotes(preferred_quote, literal, raw_content);
                            match final_content {
                                Cow::Borrowed(final_content) => {
                                    normalize_newlines(final_content, ['\r'])
                                }
                                Cow::Owned(final_content) => Cow::Owned(
                                    normalize_newlines(&final_content, ['\r']).into_owned(),
                                ),
                            }
                        }
                        Cow::Owned(s) => {
                            // content is owned, meaning we allocated a new string,
                            // so we force replacing quotes, regardless
                            let final_content = format!(
                                "{}{}{}",
                                preferred_quote.as_char(),
                                s.as_str(),
                                preferred_quote.as_char()
                            );

                            Cow::Owned(normalize_newlines(&final_content, ['\r']).into_owned())
                        }
                    }
                } else {
                    normalize_newlines(literal, ['\r'])
                }
            }
        };

        Ok(formatter.format_replaced(
            token,
            Token::from_syntax_token_cow_slice(content, token, token.text_trimmed_range().start())
                .into(),
        ))
    }
}

/// A call like expression is one of:
///
/// - [JsNewExpression]
/// - [JsImportCallExpression]
/// - [JsCallExpression]
pub(crate) fn is_call_like_expression(expression: &JsAnyExpression) -> bool {
    matches!(
        expression,
        JsAnyExpression::JsNewExpression(_)
            | JsAnyExpression::JsImportCallExpression(_)
            | JsAnyExpression::JsCallExpression(_)
    )
}
