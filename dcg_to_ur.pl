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

% EX4
%
% s(brack(X,Y)) ---> ['('], s(X), [')'], s(Y).
% s(eps) ---> [].
%
% val s : dcg = ("s", Rule (2, Functor ("brack", Var 0 :: Var 1 :: []), Left "(" :: Right ("s", Var 0) :: Left ")" :: Right ("s", Var 1) :: []) :: Rule (0, Functor ("eps", []), []) :: []) :: []


sum(add(A,B)) ---> prod(A), [+], sum(B).
sum(sub(A,B)) ---> prod(A), [-], sum(B).
sum(it(N)) ---> prod(N).

prod(mul(A,B)) ---> val(A), [*], prod(B).
prod(div(A,B)) ---> val(A), [/], prod(B).
prod(it(N)) ---> val(N).

val(num(N)) ---> num(N).
val(exp(E)) ---> ['('], sum(E), [')'].



translate_rule(Name, Clauses) -->
    ['val '], [Name], ['Rule'], [' : dcg = ('],
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
    % { Vars = 0 }, %% TODO: count variables
    ['Rule ('],[Vars],[', '],
        transform_functor(0/I, Argument),[', '],
        translate_body(I/Vars, Body),
    [')'],[' :: '].

transform_functor(I/J, V) -->
    { var(V) }, {!},
    { V = 'VARIABLE'(I) },
    ['Var '],[I],
    { J is I+1 }.
transform_functor(I/I, 'VARIABLE'(N)) -->
    ['Var '],[N].
transform_functor(I/J, F) -->
    { F =.. [Head|Params] },
    ['Functor ('],
      quote(Head), [', '],
      transform_functors(I/J, Params),
    [')'].
transform_functors(I/I, []) -->
    ['[]'].
transform_functors(I/K, [F|Fs]) -->
    transform_functor(I/J, F),
    [' :: '],
    transform_functors(J/K, Fs).

translate_body(I/K,(Command,Body)) --> {!},
    translate_command(I/J,Command),
    [' :: '],translate_body(J/K,Body).
translate_body(I/I,[]) --> {!}, ['[]'].
translate_body(I/J,Command) -->
    translate_command(I/J,Command),
    [' :: '],['[]'].

translate_command(I/I,[S]) -->
    ['Left '], quote(S).
translate_command(I/J,R) -->
    { R =.. [Rule, Arg] },
    ['Right '], ['('],
      quote(Rule),[', '],
      transform_functor(I/J, Arg),
    [')'].

quote(S) --> ['"'], [S], ['"'].

print_list([]).
print_list([X|Xs]) :- write(X), print_list(Xs).

%%

compile :-
    setof(Rule, X^Y^((X ---> Y), functor(X, Rule, 1)), Z),
    compile_rules(Z).

compile_rules([]).
compile_rules([Rule|Rules]) :-
    compile_rule(Rule), compile_rules(Rules).

compile_rule(Rule) :-
    findall((X ---> Y), ((X ---> Y), functor(X, Rule, 1)), Z),
    translate_rule(Rule, Z, Ur, []),
    print_list(Ur), nl.

:- compile.
