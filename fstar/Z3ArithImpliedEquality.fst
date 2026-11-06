module Z3ArithImpliedEquality

(* Arithmetic `th-lemma` steps tagged `implied-eq` conclude an equality
   `a = b` between numeric terms from linear premises (bounds, equalities,
   and negated bounds), without any Farkas coefficients. An equality holds
   iff both `a <= b` and `a >= b` hold, and each bound is checked by the
   existing verified Farkas kernel (`Z3LinearArithmeticAst.check`), including
   its per-literal integer strengthening of strict integer literals.

   The coefficients for each bound are found by an untrusted Fourier-Motzkin
   search below. The search is outside the soundness argument: every
   candidate is replayed by `A.check` on the actual premises. *)

#set-options "--smtencoding.elim_box true --smtencoding.nl_arith_repr native"

open FStar.Real
open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
module L = FStar.List.Tot
module A = Z3LinearArithmeticAst
module P = Z3LinearArithmeticTheory
module E = Z3LinearArithmeticEmbed
module R = Z3ArithmeticRewrite

(* ---------------- Untrusted coefficient search ---------------- *)

(* A row denotes the combination `sum_k weights_k * base_k`, whose linear
   part is `terms` and whose constant is `konst`; it claims
   `terms + konst <= 0` (`< 0` when strict). *)
type row = {
  terms: list (int & expr);
  konst: int;
  strict: bool;
  weights: list int;
}

let rec nonzero_terms (ms:list (int & expr)) : Tot (list (int & expr)) (decreases ms) =
  match ms with
  | [] -> []
  | (c, v) :: rest -> if c = 0 then nonzero_terms rest else (c, v) :: nonzero_terms rest

let normalize_terms (ms:list (int & expr)) : list (int & expr) =
  nonzero_terms (P.collect ms [])

let scale_terms (n:int) (ms:list (int & expr)) : list (int & expr) =
  L.map (fun (m:int & expr) -> (n * fst m, snd m)) ms

let rec coefficient_of (v:expr) (ms:list (int & expr)) : Tot int (decreases ms) =
  match ms with
  | [] -> 0
  | (c, w) :: rest -> if w = v then c else coefficient_of v rest

let rec unit_weights (n:nat) (k:int) (s:int) : Tot (list int) (decreases n) =
  if n = 0 then [] else (if k = 0 then s else 0) :: unit_weights (n - 1) (k - 1) s

let rec combine_weights (a b:int) (xs ys:list int) : Tot (list int) (decreases xs) =
  match xs, ys with
  | x :: xs', y :: ys' -> (a * x + b * y) :: combine_weights a b xs' ys'
  | _, _ -> []

let abs_int (n:int) : nat = if n >= 0 then n else -n

let rec gcd (a b:nat) : Tot nat (decreases b) =
  if b = 0 then a else gcd b (a % b)

let rec gcd_terms (g:nat) (ms:list (int & expr)) : Tot nat (decreases ms) =
  match ms with
  | [] -> g
  | (c, _) :: rest -> gcd_terms (gcd g (abs_int c)) rest

let rec gcd_ints (g:nat) (xs:list int) : Tot nat (decreases xs) =
  match xs with
  | [] -> g
  | x :: rest -> gcd_ints (gcd g (abs_int x)) rest

(* Dividing by a positive common divisor preserves the row's meaning. *)
let reduce (r:row) : row =
  let g = gcd_ints (gcd_terms (abs_int r.konst) r.terms) r.weights in
  if g <= 1 then r
  else { terms = L.map (fun (m:int & expr) -> (fst m / g, snd m)) r.terms;
         konst = r.konst / g; strict = r.strict;
         weights = L.map (fun (x:int) -> x / g) r.weights }

let base_row (n k:nat) (s:int) (c:A.contribution) : row =
  { terms = normalize_terms (scale_terms s c.P.poly.P.mono);
    konst = s * c.P.poly.P.cst;
    strict = c.P.strict && s > 0;
    weights = unit_weights n k s }

let positive_equality (positive:bool) (e:expr) : bool =
  match A.literal 16 positive e with
  | Some (true, A.Eq, _, _) -> true
  | _ -> false

let unit_coefficient : A.coefficient = (1, 1)

(* Rows of the unit-weight contributions; positive equalities may be used
   with either sign. Literals outside the linear fragment are omitted, which
   corresponds to weight zero. *)
let rec base_rows (lits:list (bool & expr)) (n k:nat) : Tot (list row) (decreases lits) =
  match lits with
  | [] -> []
  | (p, e) :: rest ->
    let tail = base_rows rest n (k + 1) in
    match A.prepare_literal unit_coefficient p e with
    | None -> tail
    | Some c ->
      if positive_equality p e
      then base_row n k 1 c :: base_row n k (-1) c :: tail
      else base_row n k 1 c :: tail

let rec denominators (lits:list (bool & expr)) : Tot (list pos) (decreases lits) =
  match lits with
  | [] -> []
  | (p, e) :: rest ->
    (match A.prepare_literal unit_coefficient p e with
     | Some c -> c.P.poly.P.denom
     | None -> 1) :: denominators rest

let refuted (r:row) : bool =
  r.terms = [] && (r.konst > 0 || (r.strict && r.konst >= 0))

let rec find_refuted (rows:list row) : Tot (option row) (decreases rows) =
  match rows with
  | [] -> None
  | r :: rest -> if refuted r then Some r else find_refuted rest

let rec count_sign (v:expr) (positive:bool) (rows:list row) : Tot nat (decreases rows) =
  match rows with
  | [] -> 0
  | r :: rest ->
    let c = coefficient_of v r.terms in
    (if (positive && c > 0) || (not positive && c < 0) then 1 else 0) +
    count_sign v positive rest

(* Eliminate the leading variable whose elimination creates fewest rows. *)
let rec choose (all:list row) (rows:list row) (best:option (expr & nat))
  : Tot (option (expr & nat)) (decreases rows) =
  match rows with
  | [] -> best
  | r :: rest ->
    (match r.terms with
     | [] -> choose all rest best
     | (_, v) :: _ ->
       let cost = count_sign v true all * count_sign v false all in
       (match best with
        | Some (_, b) -> if b <= cost then choose all rest best
                         else choose all rest (Some (v, cost))
        | None -> choose all rest (Some (v, cost))))

let combine (v:expr) (r1 r2:row) : row =
  let a = coefficient_of v r1.terms in
  let b = - (coefficient_of v r2.terms) in
  reduce { terms = normalize_terms (scale_terms b r1.terms `L.append` scale_terms a r2.terms);
           konst = b * r1.konst + a * r2.konst;
           strict = r1.strict || r2.strict;
           weights = combine_weights b a r1.weights r2.weights }

let useful (r:row) : bool = Cons? r.terms

let rec pair_with (v:expr) (r1:row) (negatives:list row) : Tot (list row) (decreases negatives) =
  match negatives with
  | [] -> []
  | r2 :: rest -> combine v r1 r2 :: pair_with v r1 rest

let rec pairs (v:expr) (positives negatives:list row) : Tot (list row) (decreases positives) =
  match positives with
  | [] -> []
  | r1 :: rest -> pair_with v r1 negatives `L.append` pairs v rest negatives

let sign (n:int) : int = if n > 0 then 1 else if n < 0 then -1 else 0

let rec with_sign (v:expr) (s:int) (rows:list row) : Tot (list row) (decreases rows) =
  match rows with
  | [] -> []
  | r :: rest ->
    if sign (coefficient_of v r.terms) = s then r :: with_sign v s rest else with_sign v s rest

let rec retained (rows:list row) : Tot (list row) (decreases rows) =
  match rows with
  | [] -> []
  | r :: rest -> if useful r || refuted r then r :: retained rest else retained rest

let row_limit : nat = 512

let rec fourier_motzkin (fuel:nat) (rows:list row) : Tot (option row) (decreases fuel) =
  match find_refuted rows with
  | Some r -> Some r
  | None ->
    if fuel = 0 || L.length rows > row_limit then None
    else match choose rows rows None with
    | None -> None
    | Some (v, _) ->
      let positives = with_sign v 1 rows in
      let negatives = with_sign v (-1) rows in
      let rest = with_sign v 0 rows in
      let next = retained (pairs v positives negatives `L.append` rest) in
      fourier_motzkin (fuel - 1) next

let rec coefficients (ws:list int) (ds:list pos) : Tot (list A.coefficient) (decreases ws) =
  match ws, ds with
  | w :: ws', d :: ds' -> (w * d, 1) :: coefficients ws' ds'
  | _, _ -> []

let search (lits:list (bool & expr)) : option (list A.coefficient) =
  let n = L.length lits in
  match fourier_motzkin 64 (base_rows lits n 0) with
  | Some r -> Some (coefficients r.weights (denominators lits))
  | None -> None

(* ---------------- Checked rule ---------------- *)

let bound_decl (name:string) (tag:decl_kind) (s:sort) : func_decl =
  { decl_name = name; domain = [s; s]; range = bool_sort; interp = Some tag; int_params = [] }

let le_expr (a b:expr) : expr = App (bound_decl "<=" op_arith_le (get_sort a)) [a; b]
let ge_expr (a b:expr) : expr = App (bound_decl ">=" op_arith_ge (get_sort a)) [a; b]

let bound_check (facts:list expr) (bound:expr) : bool =
  match search (A.assumptions bound facts) with
  | Some cs -> A.check cs bound facts
  | None -> false

let fact_limit : nat = 64

let numeric_equality (e:expr) : bool =
  match e with
  | App f [a; b] ->
    f = eq_decl (get_sort a) && A.numeric_sort (get_sort a) && get_sort b = get_sort a
  | _ -> false

(* `a = b` from the premises. *)
let equality_consequence (facts:list expr) (e:expr) : bool =
  match e with
  | App f [a; b] ->
    numeric_equality e && L.length facts <= fact_limit &&
    bound_check facts (le_expr a b) && bound_check facts (ge_expr a b)
  | _ -> false

(* A clause `(or (= a b) l1 ... ln)`, as in premise-free arithmetic axioms:
   both `(or (<= a b) l1 ... ln)` and `(or (>= a b) l1 ... ln)` are checked. *)
let equality_clause (facts:list expr) (e:expr) : bool =
  match e with
  | App f (App g [a; b] :: rest) ->
    f.decl_name = "or" && numeric_equality (App g [a; b]) &&
    L.length facts + L.length rest <= fact_limit &&
    bound_check facts (App f (le_expr a b :: rest)) &&
    bound_check facts (App f (ge_expr a b :: rest))
  | _ -> false

let implied_equality (facts:list expr) (e:expr) : bool =
  equality_consequence facts e || equality_clause facts e

let lemma_bound_check (facts:list expr) (bound:expr) (i:interpretation value) (rho:env value)
  : Lemma (requires (exists (nu:value -> real). E.numeric_model i nu) /\
                    Z3ObservationalEquality.boolean_model i /\ not_sound i /\ eq_sound i /\
                    or_sound i /\ conj_holds i rho facts /\ bound_check facts bound)
          (ensures lit_true i rho bound) =
  match search (A.assumptions bound facts) with
  | Some cs -> E.lemma_check_with_numeric_model cs bound facts i rho
  | None -> ()

let lemma_comparison_holds (e a b:expr) (r:A.relation)
                           (i:interpretation value) (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_operators i nu /\ A.comparison e == Some (r, a, b) /\
                    r <> A.Eq /\ lit_true i rho e)
          (ensures E.numeric_relation r (nu (eval i a rho)) (nu (eval i b rho))) =
  let comparisons (e a b:expr) (rho:env value) (r:A.relation) : prop =
    A.comparison e == Some (r, a, b) /\ r <> A.Eq ==>
    (lit_true i rho e <==> E.numeric_relation r (nu (eval i a rho)) (nu (eval i b rho))) in
  assert (forall (e a b:expr) (rho:env value) (r:A.relation). comparisons e a b rho r);
  assert (comparisons e a b rho r)

let lemma_bounds_equal (a b:expr) (i:interpretation value) (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_model i nu /\ A.numeric_sort (get_sort a) /\
                    get_sort b == get_sort a /\
                    lit_true i rho (le_expr a b) /\ lit_true i rho (ge_expr a b))
          (ensures eval i a rho == eval i b rho) =
  assert (A.comparison (le_expr a b) == Some (A.Le, a, b));
  assert (A.comparison (ge_expr a b) == Some (A.Ge, a, b));
  lemma_comparison_holds (le_expr a b) a b A.Le i nu rho;
  lemma_comparison_holds (ge_expr a b) a b A.Ge i nu rho;
  R.lemma_numeric_values_equal a b i nu rho

let lemma_both_bounds (a b:expr) (i:interpretation value) (rho:env value)
  : Lemma (requires (exists (nu:value -> real). E.numeric_model i nu) /\
                    A.numeric_sort (get_sort a) /\ get_sort b == get_sort a /\
                    lit_true i rho (le_expr a b) /\ lit_true i rho (ge_expr a b))
          (ensures eval i a rho == eval i b rho) =
  FStar.Classical.exists_elim (eval i a rho == eval i b rho)
    #(value -> real) #(fun nu -> E.numeric_model i nu) ()
    (fun nu -> lemma_bounds_equal a b i nu rho)

let lemma_equality_consequence (facts:list expr) (e:expr) (i:interpretation value) (rho:env value)
  : Lemma (requires (exists (nu:value -> real). E.numeric_model i nu) /\
                    Z3ObservationalEquality.boolean_model i /\ not_sound i /\ eq_sound i /\
                    or_sound i /\ conj_holds i rho facts /\ equality_consequence facts e)
          (ensures lit_true i rho e) =
  match e with
  | App f [a; b] ->
    lemma_bound_check facts (le_expr a b) i rho;
    lemma_bound_check facts (ge_expr a b) i rho;
    lemma_both_bounds a b i rho

let lemma_equality_clause (facts:list expr) (e:expr) (i:interpretation value) (rho:env value)
  : Lemma (requires (exists (nu:value -> real). E.numeric_model i nu) /\
                    Z3ObservationalEquality.boolean_model i /\ not_sound i /\ eq_sound i /\
                    or_sound i /\ conj_holds i rho facts /\ equality_clause facts e)
          (ensures lit_true i rho e) =
  match e with
  | App f (App g [a; b] :: rest) ->
    let le = le_expr a b in
    let ge = ge_expr a b in
    lemma_bound_check facts (App f (le :: rest)) i rho;
    lemma_bound_check facts (App f (ge :: rest)) i rho;
    assert (clause_holds i rho (le :: rest));
    assert (clause_holds i rho (ge :: rest));
    FStar.Classical.excluded_middle (clause_holds i rho rest);
    FStar.Classical.or_elim #(clause_holds i rho rest) #(~(clause_holds i rho rest))
      #(fun () -> clause_holds i rho (App g [a; b] :: rest))
      (fun _ -> ())
      (fun _ -> lemma_both_bounds a b i rho)

let lemma_implied_equality (facts:list expr) (e:expr) (i:interpretation value) (rho:env value)
  : Lemma (requires (exists (nu:value -> real). E.numeric_model i nu) /\
                    Z3ObservationalEquality.boolean_model i /\ not_sound i /\ eq_sound i /\
                    or_sound i /\ conj_holds i rho facts /\ implied_equality facts e)
          (ensures lit_true i rho e) =
  if equality_consequence facts e then lemma_equality_consequence facts e i rho
  else lemma_equality_clause facts e i rho
