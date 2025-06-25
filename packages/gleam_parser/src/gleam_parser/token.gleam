pub type Token {
  // Literals
  String(String)
  Number(String)
  Identifier(String)
  
  // Single-character tokens
  LeftParen
  RightParen
  LeftBrace
  RightBrace
  LeftBracket
  RightBracket
  Comma
  Dot
  Minus
  Plus
  Semicolon
  Star
  Slash
  
  // One or two character tokens
  Bang
  BangEqual
  Equal
  EqualEqual
  Greater
  GreaterEqual
  Less
  LessEqual
  
  // Multi-character tokens
  Arrow        // ->
  DotDot       // ..
  PipePipe     // ||
  
  // EYG-specific tokens
  At           // @
  Colon        // :
  Pipe         // |
  Hash         // #
  
  // Keywords
  And
  Else
  If
  Nil
  Or
  Match
  Perform
  Handle
  Not
  Underscore   // _
  
  // Special tokens
  Eof
  UnterminatedString(String)
  UnexpectedGrapheme(String)
}

pub fn to_string(token: Token) -> String {
  case token {
    String(value) -> "String(\"" <> value <> "\")"
    Number(value) -> "Number(" <> value <> ")"
    Identifier(value) -> "Identifier(" <> value <> ")"
    LeftParen -> "LeftParen"
    RightParen -> "RightParen"
    LeftBrace -> "LeftBrace"
    RightBrace -> "RightBrace"
    LeftBracket -> "LeftBracket"
    RightBracket -> "RightBracket"
    Comma -> "Comma"
    Dot -> "Dot"
    Minus -> "Minus"
    Plus -> "Plus"
    Semicolon -> "Semicolon"
    Star -> "Star"
    Slash -> "Slash"
    Bang -> "Bang"
    BangEqual -> "BangEqual"
    Equal -> "Equal"
    EqualEqual -> "EqualEqual"
    Greater -> "Greater"
    GreaterEqual -> "GreaterEqual"
    Less -> "Less"
    LessEqual -> "LessEqual"
    Arrow -> "Arrow"
    DotDot -> "DotDot"
    PipePipe -> "PipePipe"
    At -> "At"
    Colon -> "Colon"
    Pipe -> "Pipe"
    Hash -> "Hash"
    And -> "And"
    Else -> "Else"
    If -> "If"
    Nil -> "Nil"
    Or -> "Or"
    Match -> "Match"
    Perform -> "Perform"
    Handle -> "Handle"
    Not -> "Not"
    Underscore -> "Underscore"
    Eof -> "Eof"
    UnterminatedString(value) -> "UnterminatedString(\"" <> value <> "\")"
    UnexpectedGrapheme(value) -> "UnexpectedGrapheme(\"" <> value <> "\")"
  }
}

// Convert to canonical test format: "TOKEN_TYPE lexeme literal"
pub fn to_canonical_string(token: Token, lexeme: String, literal: String) -> String {
  let token_type = case token {
    String(_) -> "STRING"
    Number(_) -> "NUMBER"
    Identifier(_) -> "IDENTIFIER"
    LeftParen -> "LEFT_PAREN"
    RightParen -> "RIGHT_PAREN"
    LeftBrace -> "LEFT_BRACE"
    RightBrace -> "RIGHT_BRACE"
    LeftBracket -> "LEFT_BRACKET"
    RightBracket -> "RIGHT_BRACKET"
    Comma -> "COMMA"
    Dot -> "DOT"
    Minus -> "MINUS"
    Plus -> "PLUS"
    Semicolon -> "SEMICOLON"
    Star -> "STAR"
    Slash -> "SLASH"
    Bang -> "BANG"
    BangEqual -> "BANG_EQUAL"
    Equal -> "EQUAL"
    EqualEqual -> "EQUAL_EQUAL"
    Greater -> "GREATER"
    GreaterEqual -> "GREATER_EQUAL"
    Less -> "LESS"
    LessEqual -> "LESS_EQUAL"
    Arrow -> "ARROW"
    DotDot -> "DOT_DOT"
    PipePipe -> "PIPE_PIPE"
    At -> "AT"
    Colon -> "COLON"
    Pipe -> "PIPE"
    Hash -> "HASH"
    And -> "AND"
    Else -> "ELSE"
    If -> "IF"
    Nil -> "NIL"
    Or -> "OR"
    Match -> "MATCH"
    Perform -> "PERFORM"
    Handle -> "HANDLE"
    Not -> "NOT"
    Underscore -> "UNDERSCORE"
    Eof -> "EOF"
    UnterminatedString(_) -> "UNTERMINATED_STRING"
    UnexpectedGrapheme(_) -> "UNEXPECTED_GRAPHEME"
  }
  
  let literal_part = case literal {
    "" -> "null"
    _ -> literal
  }
  
  token_type <> " " <> lexeme <> " " <> literal_part
}