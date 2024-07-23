query(N) :- Min = 1, Max = 10, Min =< N, N =< Max.
go :- query(5).
