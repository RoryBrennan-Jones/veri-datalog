person(adria).
person(barrett).
person(carson).
person(deidra).
person(eldon).
person(fern).
person(gonzalo).
person(harley).
person(ignacia).
person(kati).
person(lauretta).
person(mayra).
person(noe).
person(odell).
person(reanna).
person(sona).
person(terra).
person(ursula).
person(virgilio).

parentof(adria, carson).
parentof(barrett, carson).
parentof(adria, deidra).
parentof(barrett, deidra).
parentof(deidra, eldon).
parentof(deidra, fern).
parentof(carson, gonzalo).
parentof(carson, harley).

parentof(ignacia, lauretta).
parentof(kati, lauretta).
parentof(lauretta, mayra).
parentof(mayra, noe).
parentof(mayra, odell).
parentof(noe, reanna).
parentof(noe, sona).
parentof(odell, terra).
parentof(odell, ursula).
parentof(ursula, virgilio).

siblings(X, Y) :-
    person(X),
    person(Y),
    parentof(Parent, X),
    parentof(Parent, Y).

ancestor(Parent, Child) :- parentof(Parent, Child).
ancestor(Ancestor, Descendant) :- parentof(Ancestor, Intermediate), ancestor(Intermediate, Descendant).

query(X, Y) :-
    ancestor(X, Y).