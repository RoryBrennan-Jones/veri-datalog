port_name(call,      'call').
port_name(exit,      'exit').
port_name(fail,      'fail').
port_name(redo(_),   'redo').
port_name(unify,     'unify').
port_name(exception, 'exception').

prolog_trace_interception(Port, Frame, Choice, continue) :- % _Choice
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

    %%%
    % prolog_frame_attribute(Frame, has_alternatives, Has_alternatives),
    % write("\t"),
    % write(Has_alternatives),
    % write("\t[["),
    % Has_alternatives,
    % prolog_frame_attribute(Frame, alternative, Alternative),
    % write(Alternative),
    % write("]]"),

    % prolog_choice_attribute(Choice, type, ChoiceType),
    % deterministic(D1),
    write("\t"),
    (
        \+ prolog_frame_attribute(Frame, parent, _Parent)
        ->
            prolog_choice_attribute(Choice, frame, ChoiceFrame),
            prolog_frame_attribute(ChoiceFrame, goal, ChoiceGoal),
            write(ChoiceGoal)
        ;
            write(Goal)
    ),

    %write("\t"),
    %(
    %    prolog_frame_attribute(Frame, clause, ClauseRef)
    %    ->
    %        clause_property(ClauseRef, line_count(LineCount)),
    %        write(LineCount),
    %        write(" "),
    %        nth_clause(Pred, Index, ClauseRef),
    %        write(Pred),
    %        write(" "),
    %        write(Index)
    %    ;
    %        write(0)
    %),
    %%%

    writeln(";").

:- visible(+all).
:- leash(-all).
:- include(connectivity2).
:- trace, query(n0,m3), notrace. % query(n0, n3)
:- halt.
