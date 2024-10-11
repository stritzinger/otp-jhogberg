Nonterminals modulo expression expressions vars binary_op inf_op.

Terminals '(' ')' function varname bool int distinct 'declare-const' 'declare-fun' assert 'check-sat' 'get-model' 'and' '<=' '>=' '<' '>' '=' '*' '+' '-'.

Rootsymbol modulo.

binary_op -> '<=' : numeric_le.
binary_op -> '>=' : numeric_ge.
binary_op -> '>' : numeric_gt.
binary_op -> '<' : numeric_lt.
inf_op -> '=' : same.
inf_op -> 'and' : 'and'.
inf_op -> '+' : numeric_addition.
inf_op -> '-' : numeric_subtraction.
inf_op -> '*' : numeric_multiplication.
expression -> varname : value('$1').
expression -> bool : {'Bool' , value('$1')}. % hardcoded always integer
expression -> int : {'Int' , list_to_integer(value('$1'))}. % hardcoded always integer
vars -> varname : [value('$1')].
vars -> varname vars : [value('$1')|'$2'].
expression -> 'check-sat' : 'check-sat'.
expression -> assert : assert.
expression -> 'get-model' : 'get-model'.
expression -> '(' expression ')' : {'$2'}.
expression -> '(' assert expression ')' : {assert, '$3'}.
expression -> '(' 'declare-const' varname varname ')' : {constant, value('$3'), value('$4')}.
expression -> '(' 'declare-fun' varname '(' vars ')' varname ')' : {uninterpreted_function, value('$3'), '$5', value('$7')}.
expression -> '(' distinct vars ')' : {distinct, '$3'}.
expression -> '(' inf_op expressions ')' : {'$2', '$3'}.
expression -> '(' binary_op expression expression ')' : {'$2' , '$3', '$4'}.
expression -> '(' varname expressions ')' : {value('$2') , '$3' }.

expressions -> expression  : ['$1'].
expressions -> expression expressions : ['$1' | '$2'].


modulo -> expressions : '$1'.


Erlang code.

value({_, V}) -> V.
