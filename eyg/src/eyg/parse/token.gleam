

pub type Token {
  // Literals
  String(String)
  Number(String)
  Identifier(String)
  
  // Keywords
  Match
  Perform
  Handle
  And
  Else
  If
  Nil
  Or
  Not
  Underscore
  
  // Grouping
  LeftParen
  RightParen
  LeftBrace
  RightBrace
  LeftBracket
  RightBracket
  
  // Operators
  Star
  Dot
  DotDot
  Comma
  Plus
  Minus
  Semicolon
  Bang
  BangEqual
  Equal
  EqualEqual
  Less
  LessEqual
  Greater
  GreaterEqual
  Slash
  Pipe
  PipePipe
  At
  Colon
  Arrow
  Hash
  
  // Special
  Eof
  
  // Error tokens
  UnexpectedGrapheme(String)
  UnterminatedString(String)
}

pub fn to_string(token) {
  case token {
    // Literals
    String(raw) -> "\"" <> raw <> "\""
    Number(raw) -> raw
    Identifier(raw) -> raw
    
    // Keywords
    Match -> "match"
    Perform -> "perform"
    Handle -> "handle"
    And -> "and"
    Else -> "else"
    If -> "if"
    Nil -> "nil"
    Or -> "or"
    Not -> "not"
    Underscore -> "_"
    
    // Grouping
    LeftParen -> "("
    RightParen -> ")"
    LeftBrace -> "{"
    RightBrace -> "}"
    LeftBracket -> "["
    RightBracket -> "]"
    
    // Operators
    Star -> "*"
    Dot -> "."
    DotDot -> ".."
    Comma -> ","
    Plus -> "+"
    Minus -> "-"
    Semicolon -> ";"
    Bang -> "!"
    BangEqual -> "!="
    Equal -> "="
    EqualEqual -> "=="
    Less -> "<"
    LessEqual -> "<="
    Greater -> ">"
    GreaterEqual -> ">="
    Slash -> "/"
    Pipe -> "|"
    PipePipe -> "||"
    At -> "@"
    Colon -> ":"
    Arrow -> "->"
    Hash -> "#"
    
    // Special
    Eof -> ""
    
    // Error tokens
    UnexpectedGrapheme(raw) -> raw
    UnterminatedString(raw) -> "\"" <> raw
  }
}

pub fn to_canonical_string(token, lexeme, literal) {
  let token_name = case token {
    // Literals
    String(_) -> "STRING"
    Number(_) -> "NUMBER"
    Identifier(_) -> "IDENTIFIER"
    
    // Keywords
    Match -> "MATCH"
    Perform -> "PERFORM"
    Handle -> "HANDLE"
    And -> "AND"
    Else -> "ELSE"
    If -> "IF"
    Nil -> "NIL"
    Or -> "OR"
    Not -> "NOT"
    Underscore -> "UNDERSCORE"
    
    // Grouping
    LeftParen -> "LEFT_PAREN"
    RightParen -> "RIGHT_PAREN"
    LeftBrace -> "LEFT_BRACE"
    RightBrace -> "RIGHT_BRACE"
    LeftBracket -> "LEFT_BRACKET"
    RightBracket -> "RIGHT_BRACKET"
    
    // Operators
    Star -> "STAR"
    Dot -> "DOT"
    DotDot -> "DOT_DOT"
    Comma -> "COMMA"
    Plus -> "PLUS"
    Minus -> "MINUS"
    Semicolon -> "SEMICOLON"
    Bang -> "BANG"
    BangEqual -> "BANG_EQUAL"
    Equal -> "EQUAL"
    EqualEqual -> "EQUAL_EQUAL"
    Less -> "LESS"
    LessEqual -> "LESS_EQUAL"
    Greater -> "GREATER"
    GreaterEqual -> "GREATER_EQUAL"
    Slash -> "SLASH"
    Pipe -> "PIPE"
    PipePipe -> "PIPE_PIPE"
    At -> "AT"
    Colon -> "COLON"
    Arrow -> "ARROW"
    Hash -> "HASH"
    
    // Special
    Eof -> "EOF"
    
    // Error tokens
    UnexpectedGrapheme(_) -> "UNEXPECTED"
    UnterminatedString(_) -> "UNTERMINATED_STRING"
  }
  
  let literal_str = case literal {
    "" -> "null"
    _ -> literal
  }
  
  token_name <> " " <> lexeme <> " " <> literal_str
}
