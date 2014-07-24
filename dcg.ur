(* Syntax and unification *)

datatype p = Var of int
           | Functor of string * list p
           | Str of string

con substitution = list (int * p)

fun unify (sub : substitution) (a : p) (b : p) : option (p * substitution) =
    case (a, b) of
	(Var i, a) => (case List.assoc i sub of
			   None => Some (a, (i, a) :: sub)
			 | Some j => unify sub j a)
      | (b, Var j) => unify sub (Var j) b
      | (Functor (x, xs), Functor (y, ys)) => 
	if eq x y && eq (List.length xs) (List.length ys)
	then let
		fun unify' sub xs ys zs =
		    case (xs, ys) of
			([], []) => Some (Functor (x, List.rev zs), sub)
		      | (x :: xs, y :: ys) =>
			(case unify sub x y of
			     None => None
			   | Some (z, sub') => unify' sub xs ys (z :: zs))
		      | (_, _) => None
					      
	    in
		unify' sub xs ys []
	    end
	else None
      | (Str s, Str t) =>
	if eq s t
	then Some (Str s, sub)
	else None
      | (_, _) => None

fun applySubstitution (sub : substitution) (a : p) : p =
    case a of
	Var i => (case List.assoc i sub of
		      None => Var i
		    | Some j => applySubstitution sub j)
      | Functor (x, xs) => Functor (x, List.mp (applySubstitution sub) xs)
      | Str s => Str s

fun freshen (fresh : int) (a : p) =
    case a of
	Var i => Var (fresh + i)
      | Functor (s, l) => Functor (s, List.mp (freshen fresh) l)
      | Str s => Str s

(* DCG interpreter *)

datatype either a b = Left of a | Right of b
datatype rule = Rule of (int * p * list (either string (string * p)))
	      | RuleStrFrom of list char (* charset *)
	      | RuleStrExcept of list char (* exclusion charset *)
con goal = string * p
con dcg = list (string * list rule)

fun freshenRule (fresh : int) (r : rule) : rule =
    case r of
	RuleStrFrom charset => RuleStrFrom charset
      | RuleStrExcept charset => RuleStrExcept charset
      | Rule (i, p, l) => Rule (i, freshen fresh p, List.mp (fn e => case (e : either string (string * p)) of
									 Left x => Left x
								       | Right y => Right (y.1, freshen fresh y.2)) l)
(*
fun vars' (r : rule) : int = case r of Rule (vars, _, _) => vars
fun head' (r : rule) : p = case r of Rule (_, head, _) => head
fun body' (r : rule) : list (either string goal) = case r of Rule (_, _, body) => body
*)
fun stroccurs (needle : string) (haystack : string) (index : int) =
    if strlen haystack < index + strlen needle
    then False
    else eq needle (substring haystack index (strlen needle))

fun breakFrom (test : char -> bool) (str : string) (index : int) : string * int =
    let
	fun breakIndex (i : int) =
	    if strlenGe str (index + i + 1) && test (strsub str (index + i))
	    then breakIndex (i + 1)
	    else i
    in
	(substring str index (breakIndex 0), index + (breakIndex 0))
    end
(*
fun breakTest (s : string) : transaction page =
    let
	val a = (breakFrom isdigit "abc123456789asdfasdfasdfafsdwer" 3)
    in
	return <xml><body>{[a.1]}</body></xml>
    end
*)

fun runDCG (fresh : int) (sub : substitution) (prg : dcg) (goalp : goal) (input : int * string) (choices : int) : option (int * p * substitution * int * (int * string)) =
    case List.assoc goalp.1 prg of
	None => None
      | Some rules =>
	case goalp of
	    (goal,p) =>
	    let
		fun loop (n : int) (rules : list rule) : option (int * p * substitution * int * (int * string)) =
		    case rules of
			[] => None
		      | (RuleStrFrom charset) :: rules => (case breakFrom (fn c => List.exists (eq c) charset) input.2 input.1 of
							       (frag, index) => case unify sub (Str frag) p of
										    Some (result, sub) => Some (fresh, result, sub, n, (index, input.2))
										  | None => loop (n+1) rules)
		      | (RuleStrExcept charset) :: rules => (case breakFrom (fn c => not (List.exists (eq c) charset)) input.2 input.1 of
								 (frag, index) => case unify sub (Str frag) p of
										      Some (result, sub) => Some (fresh, result, sub, n, (index, input.2))
										    | None => loop (n+1) rules)
		      | (Rule (vars', head', body')) :: rules =>
			case unify sub head' p of
			    Some (result, sub) => (case runGoals (fresh + vars') sub prg (body') input result of
						       Some (fresh, result, sub, input) => Some (fresh, result, sub, n, input)
						     | None => loop (n+1) rules)
			  | None => loop (n+1) rules
	    in
		loop choices (List.drop choices (List.mp (freshenRule fresh) rules))
	    end

and runGoals (fresh : int) (sub : substitution) (prg : dcg) (goals : list (either string goal)) (input : int * string) (result : p) : option (int * p * substitution * (int * string)) =
    case goals of
	[] => Some (fresh, result, sub, input)
      | goal :: goals =>
	case goal of
	    Left str => (case input of
			     (index, text) => if stroccurs str text index
					      then runGoals fresh sub prg goals (index+strlen str,text) result
					      else None)
	  | Right goal =>
	    let
		fun loop (i : int) =
		    case runDCG fresh sub prg goal input i of
			Some (fresh, _, sub, j, input) => (case runGoals fresh sub prg goals input (applySubstitution sub result) of
							       Some r => Some r
							     | None => loop (j + 1))
		      | None => None
	    in
		loop 0
	    end

(* Examples/Testing *)

val test1 : dcg = ("test", (Rule (0, Functor ("foo", []), Left "foo" :: Left "bar" :: [])) :: []) :: []
val test2 : dcg = ("test", (Rule (0, Functor ("foo", []), Left "foo" :: [])) ::
                           (Rule (0, Functor ("bar", []), Left "bar" :: [])) ::
                           []) :: []
val test3 : dcg = ("foobar", (Rule (0, Functor ("foo", []), Left "foo" :: [])) ::
                             (Rule (0, Functor ("bar", []), Left "bar" :: [])) ::
                             []) ::
		  ("test", (Rule (1, Var 0, Right ("foobar", Var 0) :: Left "-" :: Right ("foobar", Var 0) :: []) :: [])) ::
		  []
val test4 : dcg = ("test", (RuleStrFrom (#"0" :: #"1" :: #"2" :: #"3" :: #"4" :: #"5" :: #"6" :: #"7" :: #"8" :: #"9" :: [])) :: []) :: []

(*
 * S ::= '(' S ')' S | epsilon
 * % s(brack(X,Y)) --> [(], s(X), [)], s(Y)
 * % s(eps) --> []
 *)
val brackets : dcg = ("s", Rule (2, Functor ("brack", Var 0 :: Var 1 :: []), Left "(" :: Right ("s", Var 0) :: Left ")" :: Right ("s", Var 1) :: []) :: Rule (0, Functor ("eps", []), []) :: []) :: []


val numRule = ("num", RuleStrFrom (#"0" :: #"1" :: #"2" :: #"3" :: #"4" :: #"5" :: #"6" :: #"7" :: #"8" :: #"9" :: []) :: [])
val sumRule = ("sum", Rule (2, Functor ("add", Var 0 :: Var 1 :: []), Right ("prod", Var 0) :: Left "+" :: Right ("sum", Var 1) :: []) :: Rule (2, Functor ("sub", Var 0 :: Var 1 :: []), Right ("prod", Var 0) :: Left "-" :: Right ("sum", Var 1) :: []) :: Rule (1, Functor ("it", Var 0 :: []), Right ("prod", Var 0) :: []) :: [])
val prodRule = ("prod", Rule (2, Functor ("mul", Var 0 :: Var 1 :: []), Right ("val", Var 0) :: Left "*" :: Right ("prod", Var 1) :: []) :: Rule (2, Functor ("div", Var 0 :: Var 1 :: []), Right ("val", Var 0) :: Left "/" :: Right ("prod", Var 1) :: []) :: Rule (1, Functor ("it", Var 0 :: []), Right ("val", Var 0) :: []) :: [])
val valRule = ("val", Rule (1, Functor ("num", Var 0 :: []), Right ("num", Var 0) :: []) :: Rule (1, Functor ("exp", Var 0 :: []), Left "(" :: Right ("sum", Var 0) :: Left ")" :: []) :: [])

val arithmeticRules : dcg = numRule :: prodRule :: sumRule :: valRule :: []

fun displayArithmetic (arith : p) : xbody =
    case arith of
	Str s => <xml>{[s]}</xml>
      | Functor ("it", i :: []) => displayArithmetic i
      | Functor ("num", i :: []) => displayArithmetic i
      | Functor ("exp", i :: []) => displayArithmetic i
      | Functor (op, p :: q :: []) =>
	<xml>
	  <ul>
	    <li>{[op]}</li>
	    <li>{displayArithmetic p}</li>
	    <li>{displayArithmetic q}</li>
	  </ul>
	</xml>
      | _ => <xml><b>This should not happen</b></xml>

val colors = (STYLE "color: red") :: (STYLE "color: orange") :: (STYLE "color: green") :: (STYLE "color: blue") :: (STYLE "color: indigo") :: (STYLE "color: violet") :: []

fun displayBrackets colors (brackets : p) : xbody =
    case brackets of
	Functor ("eps", []) => <xml/>
      | Functor ("brack", x :: y :: []) => (case colors of
						c :: colors => <xml>
						  <span style={c}>(</span>
						  {displayBrackets (List.append colors (c :: [])) x}
						  <span style={c}>)</span>
						  {displayBrackets (List.append colors (c :: [])) y}
						</xml>
					      | _ => <xml><b>This should not happen</b></xml>)
      | _ => <xml><b>This should not happen</b></xml> (* COMPILER ISSUE: NOT ABLE TO USE ERROR HERE *)

fun g p q s = case runDCG 1 [] p (q, Var 0) (0,s) 0 of
	      None => <xml>no parse</xml>
	    | Some (_,p,_,_,(i,_)) => <xml><span style={STYLE "font-size: 5em"}>{displayBrackets colors p}</span></xml>

fun f p q s = case runDCG 1 [] p (q, Var 0) (0,s) 0 of
	      None => <xml>no parse</xml>
	    | Some (_,p',_,_,(i,_)) => <xml>{displayArithmetic p'}</xml>

(*
fun f p q s = case runDCG 1 [] p (q, Var 0) (0,s) 0 of
	      None => <xml>no parse</xml>
	    | Some (_,p,_,_,(i,_)) =>
	      case p of
		  Str i => <xml>{[i]}</xml>
		| _ => <xml>no good parse</xml>
*)

fun main s : transaction page =
    return <xml><body>
      
      <a link={parens "((())()(((()))))(()(()(()(()))))(())(())"}>brackets</a>
      
      <form>
	<textbox{#Text} value="1+2*3+4*(5+6)*7"/>
	<submit action={moo}/>
      </form>
    
    </body></xml>

and moo s : transaction page =
    return <xml><body>
      <form>
	<textbox{#Text}/>
	<submit action={moo}/>
	<hr/>
      </form>
	{f arithmeticRules "sum" s.Text}
    </body></xml>

and parens s : transaction page =
    return <xml><body>
      {g brackets "s" s}
    </body></xml>
    


(* EXAMPLE http://127.0.0.1:8080/Dcg/main/8 *)
