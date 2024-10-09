Nonterminals modulo expression expressions.

Terminals '(' ')' type set_logic declare_const assert check_sat op varname value exit.

Rootsymbol modulo.

expression -> value : '$1'.
expression -> varname : '$1'.
expression -> '(' op expression expression ')' : {op, '$3', '$4'}.
expression -> '(' set_logic type ')' : {set_logic, '$3'}.
expression -> '(' declare_const varname type ')' : {declare_const, '$3', '$4'}.
expression -> '(' assert expression ')' : {assert, '$3'}.
expression -> '(' check_sat ')' : {check_sat}.
expression -> '(' exit ')' : {exit}.
expressions -> expression expressions : ['$1'] ++ '$2'.


modulo -> expressions.


Erlang code.
