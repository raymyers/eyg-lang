pub mod lexer;
pub mod parser;
pub mod token;

use eyg_ir::ast::Node;
use parser::ParseError;

pub fn from_string(source: &str) -> Result<Node, ParseError> {
    let tokens = lexer::lex(source);
    let tokens = token::drop_whitespace(tokens);
    let tokens = token::drop_comments(tokens);
    let (node, remaining) = parser::expression(&tokens)?;
    if !remaining.is_empty() {
        let (tok, pos) = &remaining[0];
        return Err(ParseError::UnexpectedToken(tok.clone(), *pos));
    }
    Ok(node)
}

pub fn block_from_string(source: &str) -> Result<Node, ParseError> {
    let tokens = lexer::lex(source);
    let tokens = token::drop_whitespace(tokens);
    let tokens = token::drop_comments(tokens);
    let (node, _remaining) = parser::block(&tokens)?;
    Ok(node)
}
