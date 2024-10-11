
Definitions.

Rules.

\( : {token, {'(',  TokenLine}}.
\) : {token, {')',  TokenLine}}.
[0-9]+ : {token, {int, TokenChars}}.
[a-z\-\=\*<>]+ :  {token, parse(TokenChars, TokenLine)}.
[A-Z_]+[a-z]+ : {token, {type, list_to_atom(TokenChars)}}.
\s+ : skip_token.
\n : skip_token.
;.* : skip_token. % Comments

Erlang code.

parse("declare-const" = T, L) -> {list_to_atom(T), L};
parse("declare-fun" = T, L) -> {list_to_atom(T), L};
parse("assert" = T, L) -> {list_to_atom(T), L};
parse("check-sat" = T, L) -> {list_to_atom(T), L};
parse("get-model" = T, L) -> {list_to_atom(T), L};
parse("<" = T, L) -> {list_to_atom(T), L};
parse(">" = T, L) -> {list_to_atom(T), L};
parse("=" = T, L) -> {list_to_atom(T), L};
parse("false", _) -> {bool, false};
parse("true", _) -> {bool, true};
parse(Token, _) -> {varname, list_to_atom(Token)}.
