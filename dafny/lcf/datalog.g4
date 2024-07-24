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
  | left=term name=Operator right=term
  ;

term
  : const
  | variable
  ;

const
  : atom
  | natural
  | string
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
  : s=Str
  ;

variable
  : name=VarName
  ;

/*
 * Lexer Rules
 */

fragment CHARACTER: ALPHANUMERIC |' '|'\t'|'\n'|'\r'|'\r\n'; // TODO: expand to all ASCII characters
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

Operator
  : '=' | '=<' | '>=' | '\\=' | '==' | '=\\='
  ;

VarName
  : LEADER (Nondigit | Digit)*
  ;

Int
	: ('-')? Digit+
	;

Nat
  : Digit+
  ;

Str
  : '"' CHARACTER* '"' 
  ;

fragment Nondigit
	: [a-zA-Z] | '_'
	;

fragment Digit
	: [0-9]
	;

WS // TODO: if this is causing whitespace in strings to be skipped, fix that (it causes parsing issues)
	: (' '|'\t'|'\n'|'\r'|'\r\n')+ -> skip
	;
