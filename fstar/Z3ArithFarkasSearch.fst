module Z3ArithFarkasSearch

(* Search for Farkas coefficients of linear arithmetic theory lemmas whose
   proof hint carries none (for example `th-lemma arith implied-eq`).

   The search is an untrusted Fourier-Motzkin elimination over the literal
   contributions of `Z3LinearArithmeticAst`. It only proposes coefficients:
   every acceptance is re-established by the verified `A.check`, so a bug in
   the search can lose coverage but never soundness. Equality conclusions,
   which `A.check` cannot negate, are split into their two non-strict halves;
   the lemma below derives the equality from both checked halves. *)

#set-options "--smtencoding.elim_box true --smtencoding.nl_arith_repr native"

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
open Z3ObservationalEquality
module L = FStar.List.Tot
module A = Z3LinearArithmeticAst
module P = Z3LinearArithmeticTheory
module LE = Z3LinearArithmeticEmbed

(* Integer-scaled linear forms with distinct terms and non-zero coefficients. *)
type terms = list (int & expr)

(* A row states `terms + constant <= 0` (`< 0` when strict, `= 0` for
   equalities). `origin` gives the multiple of each assumption's unit-weight
   contribution whose sum is the row. *)
type row = {
  terms: terms;
  constant: int;
  strict: bool;
  equality: bool;
  origin: list int;
}

let rec add_term (c:int) (v:expr) (ts:terms) : Tot terms (decreases ts) =
  match ts with
  | [] -> if c = 0 then [] else [(c, v)]
  | (k, w) :: rest ->
    if v = w then (if c + k = 0 then rest else (c + k, w) :: rest)
    else (k, w) :: add_term c v rest

let rec add_terms (n:int) (xs acc:terms) : Tot terms (decreases xs) =
  match xs with
  | [] -> acc
  | (c, v) :: rest -> add_terms n rest (add_term (n * c) v acc)

let rec coefficient_of (v:expr) (ts:terms) : Tot int (decreases ts) =
  match ts with
  | [] -> 0
  | (k, w) :: rest -> if v = w then k else coefficient_of v rest

let rec add_origin (m:int) (xs:list int) (n:int) (ys:list int)
  : Tot (list int) (decreases xs) =
  match xs, ys with
  | x :: xs', y :: ys' -> (m * x + n * y) :: add_origin m xs' n ys'
  | _, _ -> []

(* `m * r + n * s`; callers use positive `m`, and positive `n` unless `s` is
   an equality. *)
let combine (m:int) (r:row) (n:int) (s:row) : row =
  { terms = add_terms n s.terms (add_terms m r.terms []);
    constant = m * r.constant + n * s.constant;
    strict = r.strict || s.strict;
    equality = r.equality && s.equality;
    origin = add_origin m r.origin n s.origin }

let contradiction (r:row) : option (list int) =
  if Cons? r.terms then None
  else if r.equality then
    (if r.constant > 0 then Some r.origin
     else if r.constant < 0 then Some (L.map (fun (x:int) -> -x) r.origin)
     else None)
  else if (if r.strict then r.constant >= 0 else r.constant > 0) then Some r.origin
  else None

let rec first_contradiction (rows:list row) : Tot (option (list int)) (decreases rows) =
  match rows with
  | [] -> None
  | r :: rest ->
    (match contradiction r with Some o -> Some o | None -> first_contradiction rest)

let rec pivot_equality (rows:list row) : Tot (option (row & expr & int)) (decreases rows) =
  match rows with
  | [] -> None
  | r :: rest ->
    (match r.equality, r.terms with
     | true, (a, v) :: _ -> Some (r, v, a)
     | _, _ -> pivot_equality rest)

(* Eliminate `v` from `r` using the equality `e` whose `v`-coefficient is `a`. *)
let substitute (v:expr) (e:row) (a:int) (r:row) : row =
  let b = coefficient_of v r.terms in
  if b = 0 then r
  else if a > 0 then combine a r (-b) e
  else combine (-a) r b e

let rec substitute_all (v:expr) (e:row) (a:int) (rows:list row)
  : Tot (list row) (decreases rows) =
  match rows with
  | [] -> []
  | r :: rest ->
    if r = e then substitute_all v e a rest
    else substitute v e a r :: substitute_all v e a rest

let rec sign_counts (v:expr) (rows:list row) : Tot (nat & nat) (decreases rows) =
  match rows with
  | [] -> (0, 0)
  | r :: rest ->
    let p, n = sign_counts v rest in
    let c = coefficient_of v r.terms in
    if c > 0 then (p + 1, n) else if c < 0 then (p, n + 1) else (p, n)

(* Prefer the variable whose elimination creates the fewest rows. *)
let rec best_variable (rows:list row) (candidates:terms) (best:option (expr & int))
  : Tot (option (expr & int)) (decreases candidates) =
  match candidates with
  | [] -> best
  | (_, v) :: rest ->
    let p, n = sign_counts v rows in
    let cost = p * n - p - n in
    let best' =
      match best with
      | Some (_, c) -> if cost < c then Some (v, cost) else best
      | None -> Some (v, cost) in
    best_variable rows rest best'

let rec all_terms (rows:list row) : Tot terms (decreases rows) =
  match rows with
  | [] -> []
  | r :: rest -> r.terms `L.append` all_terms rest

let rec pair_with (v:expr) (p:row) (a:int) (negatives:list row)
  : Tot (list row) (decreases negatives) =
  match negatives with
  | [] -> []
  | n :: rest ->
    let b = coefficient_of v n.terms in
    combine (-b) p a n :: pair_with v p a rest

let rec resolvents (v:expr) (positives negatives:list row)
  : Tot (list row) (decreases positives) =
  match positives with
  | [] -> []
  | p :: rest ->
    pair_with v p (coefficient_of v p.terms) negatives `L.append` resolvents v rest negatives

(* Rows without `v`, then rows with a positive and a negative coefficient. *)
let rec partition (v:expr) (rows:list row)
  : Tot (list row & list row & list row) (decreases rows) =
  match rows with
  | [] -> ([], [], [])
  | r :: rest ->
    let keep, positives, negatives = partition v rest in
    let c = coefficient_of v r.terms in
    if c > 0 then (keep, r :: positives, negatives)
    else if c < 0 then (keep, positives, r :: negatives)
    else (r :: keep, positives, negatives)

let eliminate_variable (v:expr) (rows:list row) : list row =
  let keep, positives, negatives = partition v rows in
  keep `L.append` resolvents v positives negatives

let row_limit : nat = 256

let rec fourier_motzkin (fuel:nat) (rows:list row) : Tot (option (list int)) (decreases fuel) =
  match first_contradiction rows with
  | Some o -> Some o
  | None ->
    if fuel = 0 || L.length rows > row_limit then None
    else
      match pivot_equality rows with
      | Some (e, v, a) -> fourier_motzkin (fuel - 1) (substitute_all v e a rows)
      | None ->
        match best_variable rows (all_terms rows) None with
        | None -> None
        | Some (v, cost) ->
          (* `cost` is the change in row count, checked before resolving. *)
          if L.length rows + cost > row_limit then None
          else fourier_motzkin (fuel - 1) (eliminate_variable v rows)

let rec unit_origin (n:nat) (j:int) (d:int) : Tot (list int) (decreases n) =
  if n = 0 then [] else (if j = 0 then d else 0) :: unit_origin (n - 1) (j - 1) d

let initial_row (n j:nat) (positive:bool) (e:expr) : option row =
  match A.literal 16 positive e with
  | None -> None
  | Some (p, r, _, _) ->
    if r = A.Eq && not p then None
    else match A.prepare_literal (1, 1) positive e with
    | None -> None
    | Some c ->
      Some { terms = add_terms 1 c.P.poly.P.mono [];
             constant = c.P.poly.P.cst;
             strict = c.P.strict;
             equality = r = A.Eq;
             origin = unit_origin n j c.P.poly.P.denom }

(* Literals outside the linear fragment simply receive weight zero. *)
let rec initial_rows (n j:nat) (lits:list (bool & expr)) : Tot (list row) (decreases lits) =
  match lits with
  | [] -> []
  | (positive, e) :: rest ->
    (match initial_row n j positive e with
     | Some r -> r :: initial_rows n (j + 1) rest
     | None -> initial_rows n (j + 1) rest)

let search (lits:list (bool & expr)) : option (list A.coefficient) =
  match fourier_motzkin 64 (initial_rows (L.length lits) 0 lits) with
  | Some origin -> Some (L.map (fun (x:int) -> ((x, 1) <: A.coefficient)) origin)
  | None -> None

(* Facts entail `conclusion` by a searched, then verified, Farkas combination. *)
let farkas (conclusion:expr) (facts:list expr) : bool =
  match search (A.assumptions conclusion facts) with
  | Some cs -> A.check cs conclusion facts
  | None -> false

let comparison_decl (name:string) (tag:decl_kind) (s:sort) : func_decl =
  { decl_name = name; domain = [s; s]; range = bool_sort; interp = Some tag; int_params = [] }

let le_expr (a b:expr) : expr = App (comparison_decl "<=" op_arith_le (get_sort a)) [a; b]
let ge_expr (a b:expr) : expr = App (comparison_decl ">=" op_arith_ge (get_sort a)) [a; b]

(* A numeric equality holds when both of its non-strict halves are entailed. *)
let equality (facts:list expr) (conclusion:expr) : bool =
  match A.comparison conclusion with
  | Some (A.Eq, a, b) -> farkas (le_expr a b) facts && farkas (ge_expr a b) facts
  | _ -> false

let consequence (facts:list expr) (conclusion:expr) : bool =
  farkas conclusion facts || equality facts conclusion

(* ----------------------------------------------------------------- *)
(* Soundness                                                           *)
(* ----------------------------------------------------------------- *)

let arithmetic_model (i:interpretation value) : prop =
  (exists (nu:value -> FStar.Real.real). LE.numeric_model i nu) /\
  boolean_model i /\ not_sound i /\ eq_sound i /\ or_sound i

let lemma_farkas (i:interpretation value) (rho:env value) (conclusion:expr) (facts:list expr)
  : Lemma (requires arithmetic_model i /\ conj_holds i rho facts /\ farkas conclusion facts)
          (ensures lit_true i rho conclusion) =
  let cs = Some?.v (search (A.assumptions conclusion facts)) in
  LE.lemma_check_with_numeric_model cs conclusion facts i rho

let lemma_halves (i:interpretation value) (nu:value -> FStar.Real.real) (rho:env value)
                 (conclusion a b:expr)
  : Lemma (requires LE.numeric_model i nu /\ eq_sound i /\
                    A.comparison conclusion == Some (A.Eq, a, b) /\
                    lit_true i rho (le_expr a b) /\ lit_true i rho (ge_expr a b))
          (ensures lit_true i rho conclusion) =
  let s = get_sort a in
  assert (A.comparison (le_expr a b) == Some (A.Le, a, b));
  assert (A.comparison (ge_expr a b) == Some (A.Ge, a, b));
  let x = nu (eval i a rho) in
  let y = nu (eval i b rho) in
  assert (LE.numeric_relation A.Le x y);
  assert (LE.numeric_relation A.Ge x y);
  assert (x == y);
  if s = A.int_s then (
    assert (VInt? (eval i a rho) /\ VInt? (eval i b rho));
    let VInt m = eval i a rho in
    let VInt n = eval i b rho in
    assert (FStar.Real.of_int m == FStar.Real.of_int n);
    assert (m == n))
  else assert (eval i a rho == eval i b rho);
  match conclusion with
  | App _ [_; _] -> ()
  | _ -> ()

let lemma_equality (i:interpretation value) (rho:env value) (facts:list expr) (conclusion:expr)
  : Lemma (requires arithmetic_model i /\ conj_holds i rho facts /\ equality facts conclusion)
          (ensures lit_true i rho conclusion) =
  let _, a, b = Some?.v (A.comparison conclusion) in
  lemma_farkas i rho (le_expr a b) facts;
  lemma_farkas i rho (ge_expr a b) facts;
  FStar.Classical.exists_elim (lit_true i rho conclusion)
    #(value -> FStar.Real.real) #(fun nu -> LE.numeric_model i nu) ()
    (fun nu -> lemma_halves i nu rho conclusion a b)

let lemma_consequence (i:interpretation value) (rho:env value) (facts:list expr) (conclusion:expr)
  : Lemma (requires arithmetic_model i /\ conj_holds i rho facts /\ consequence facts conclusion)
          (ensures lit_true i rho conclusion) =
  if farkas conclusion facts then lemma_farkas i rho conclusion facts
  else lemma_equality i rho facts conclusion
