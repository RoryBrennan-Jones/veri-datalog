ends_with_dot(S) :-
  sub_string(S, _, 1, 0, E),
  E == "d".

go :- ends_with_dot("helloworld").
