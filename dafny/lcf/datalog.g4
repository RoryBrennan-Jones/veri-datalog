grammar datalog;

/*
 * Trace parser.
 */

trace
  : traceevent+ EOF
  ;

traceevent
  : port level=integer id=integer goal=clause choice=clause';'
  ;

port
  : name=Port
  ;

integer
  : numeral=Int
  ;

/*
 * Datalog program parser.
 */

program
	: (fact | rule)+ EOF
	;

fact
  : clause '.'
  ;

rule
  : clause ':-' clause_list '.'
  ;

clause
  : name=Identifier ( '(' term_list ')' )?
  ;

term
  : const
  | variable
  ;

const
  : atom
  | string
  | natural
  ;

clause_list
  : clause ( ',' clause)*
  ;

term_list
  : term ( ',' term)*
  ;

atom
  : val=Identifier
  ;

natural
  : numeral=Int // telling it to use Nat doesn't work
  ;

string
  : val=Str
  ;

variable
  : name=VarName
  ;

/*
 * Lexer Rules
 */

fragment ALPHANUMERIC: ALPHA | DIGIT ;
fragment ALPHA: '_' | SMALL_LETTER | CAPITAL_LETTER ;
fragment LEADER: '_' | CAPITAL_LETTER;
fragment SMALL_LETTER: [a-z];
fragment CAPITAL_LETTER: [A-Z];
fragment DIGIT: [0-9];

Port
  : 'call' | 'redo' | 'unify' | 'exit' | 'fail'
  ;

Identifier
	: SMALL_LETTER (Nondigit | Digit)*
	;

VarName
  : LEADER (Nondigit | Digit)*
  ;

Int
	: ('-')? Digit+
	;

///
Nat
  : Digit+
  ;

fragment CHARACTER: ' ' | '\r' | '\n' | '\t' | '_' | ALPHA | DIGIT;

Str
  : '"' CHARACTER* '"' 
  ;
///

fragment Nondigit
	: [a-zA-Z]
	;

fragment Digit
	: [0-9]
	;

WS
	: (' '|'\t'|'\n'|'\r'|'\r\n')+ -> skip
	;
