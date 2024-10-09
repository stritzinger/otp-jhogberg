
Definitions.

Rules.

\( : {token, {'(',  TokenLine}}.
% \) : {{token, {')',  TokenLine}}.
[0-9]+ : {token, {value, TokenChars}}.
set-logic : {token, {set_logic,  TokenLine}}.
declare-const : {token, {declare_const,  TokenLine}}.
assert : {token, {assert, TokenLine}}.
check-sat : {token, {check_sat,  TokenLine}}.
exit : {token, {exit,  TokenLine}}.
[a-z]+ : {token, {varname, TokenChars}}.
Int : {token, {type, TokenChars}}.
[A-Z_]+ : {token, {type, TokenChars}}.
[\+|\=] : {token, {op, TokenChars}}.
\s+ : skip_token.
\n : skip_token.
;.* : skip_token. % Comments

Erlang code.
