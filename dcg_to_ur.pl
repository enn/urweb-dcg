% swipl -q -s dcg_to_ur.pl

:- op(1200, xfx, --->).

%% EX1
%
% test1(foo) ---> [foo], [bar].
%
% :- (X ---> Y), translate_rule(X,Y,Z,[]), print_list(Z), nl.
%
% val test1 : dcg = ("test1", (Rule (0, Functor ("foo", []), Left "foo" :: Left "bar" :: [])) :: []) :: []

% EX2
%
% test2(foo) ---> [foo].
% test2(bar) ---> [bar].
%
% :- findall((X ---> Y), ((X ---> Y), functor(X, test2, 1)), Z), translate_rule(test2, Z, Ur, []), print_list(Ur), nl.
%
% val test2 : dcg = ("test2", Rule (0, Functor ("foo", []), Left "foo" :: []) :: Rule (0, Functor ("bar", []), Left "bar" :: []) :: []) :: []

% EX3
%
% test3(X) ---> test2(X), ['-'], test2(X).
%
% val test3 : dcg = ("test3", Rule (0, Var 0, Right ("test2", Var 0) :: Left "-" :: Right ("test2", Var 0) :: []) :: []) :: []

%%
%% TODO: Along with counting variable numbers create a phase that traverses the argument of the head and the arguments of the rule calls (Right) converting them to Ur terms

test3(X) ---> test2(X), ['-'], test2(X).

translate_rule(Name, Clauses) -->
    ['val '], [Name], [' : dcg = ('],
      ['\"'], [Name], ['\"'], [', '],
      translate_rule_clauses(Clauses),
    [')'],[' :: '],['[]'], % Just one goal
    [].

translate_rule_clauses([]) --> ['[]'].
translate_rule_clauses([Clause|Clauses]) -->
    translate_rule_clause(Clause),
    translate_rule_clauses(Clauses).

translate_rule_clause((Head ---> Body)) -->
    { Head =.. [_, Argument] },
    { Vars = 0 }, %% TODO: count variables
    ['Rule ('],[Vars],[', '],
        translate_argument(Argument),[', '],
        translate_body(Body),
    [')'],[' :: '].

translate_argument(Argument) -->
    { var(Argument) }, {!},
    { Argument = 'Var 0' },
    [Argument].
translate_argument(Argument) -->
    { Argument =.. [Head|Params] },
    { Params = [] }, %% NOT IMPLEMENTED YET
    ['Functor ('],
      quote(Head), [', '], ['[]'],
    [')'].

translate_body((Command,Body)) --> {!},
    translate_command(Command),
    [' :: '],translate_body(Body).
translate_body(Command) -->
    translate_command(Command),
    [' :: '],['[]'].

translate_command([S]) -->
    ['Left '], quote(S).
translate_command(R) -->
    { R =.. [Rule, Arg] },
    ['Right '], ['('],
      quote(Rule),[', '],
      [Arg],  %% TODO: handle more than just Var 0
    [')'].

quote(S) --> ['"'], [S], ['"'].

print_list([]).
print_list([X|Xs]) :- write(X), print_list(Xs).

:- findall((X ---> Y), ((X ---> Y), functor(X, test3, 1)), Z), translate_rule(test3, Z, Ur, []), print_list(Ur), nl.
