Nonterminals modulo expression expressions types binary_op.

Terminals '(' ')' function type varname bool int 'declare-const' 'declare-fun' assert 'check-sat' 'get-model' '<' '>' '='.

Rootsymbol modulo.

binary_op -> '<' : numeric_lt.
binary_op -> '>' : numeric_gt.
binary_op -> '=' : same.
expression -> varname : value('$1').
expression -> bool : {'Bool' , value('$1')}. % hardcoded always integer
expression -> int : {'Int' , list_to_integer(value('$1'))}. % hardcoded always integer
types -> type : [value('$1')].
types -> type types : [value('$1')|'$2'].
expression -> 'check-sat' : 'check-sat'.
expression -> assert : assert.
expression -> 'get-model' : 'get-model'.
expression -> '(' expression ')' : {'$2'}.
expression -> '(' assert expression ')' : {assert, '$3'}.
expression -> '(' 'declare-const' varname type ')' : {constant, value('$3'), value('$4')}.
expression -> '(' 'declare-fun' varname '(' types ')' type ')' : {uninterpreted_function, value('$3'), '$5', value('$7')}.
expression -> '(' binary_op expression expression ')' : {'$2' , '$3', '$4'}.
expression -> '(' varname expressions ')' : {value('$2') , '$3' }.

expressions -> expression  : ['$1'].
expressions -> expression expressions : ['$1' | '$2'].


modulo -> expressions : '$1'.


Erlang code.

value({_, V}) -> V.
