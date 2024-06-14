port_name(call,      'call').
port_name(exit,      'exit').
port_name(fail,      'fail').
port_name(redo(_),   'redo').
port_name(unify,     'unify').
port_name(exception, 'exception').

prolog_trace_interception(Port, Frame, _Choice, continue) :-
    port_name(Port, PortName),
    write(PortName),

    prolog_frame_attribute(Frame, level, Level),
    write("\t"),
    write(Level),

    write("\t"),
    (
        prolog_frame_attribute(Frame, clause, ClauseRef)
        ->
            clause_property(ClauseRef, line_count(LineCount)),
            write(LineCount)
        ;
            write(0)
    ),

    prolog_frame_attribute(Frame, goal, Goal),
    write("\t"),
    write(Goal),

    writeln(";").

:- visible(+all).
:- leash(-all).
:- include(connectivity2).
:- trace, query(kati, noe), notrace. % query(n0, n3)
:- halt.
