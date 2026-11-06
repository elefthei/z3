module Z3ArithImpliedEq

(* Arithmetic implied equalities.

   Z3's arithmetic solvers label equalities between two columns fixed at the
   same value as `th-lemma arith implied-eq` without Farkas coefficients. Such
   a step concludes `a = b` from bound and equality premises. This module
   splits the conclusion into `a <= b` and `a >= b`, searches for Farkas
   coefficients for both directions with an exact rational simplex, and then
   re-checks both candidate certificates with the verified kernel
   `Z3LinearArithmeticAst.check`. The two bounds give the equality through
   the verified arithmetic triangle tautology
   `(or (= a b) (not (<= a b)) (not (>= a b)))`.

   The search is untrusted: only `certified` occurs in the soundness theorem,
   so a wrong or missing search result can only leave an obligation pending. *)

#set-options "--smtencoding.elim_box true --smtencoding.nl_arith_repr native"

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
module L = FStar.List.Tot
module P = Z3LinearArithmeticTheory
module LA = Z3LinearArithmeticAst
module LE = Z3LinearArithmeticEmbed
module AR = Z3ArithmeticRewrite
module B = Z3BooleanRewrite
module OE = Z3ObservationalEquality

(* ----------------------------------------------------------------- *)
(* Checked certificate                                                 *)
(* ----------------------------------------------------------------- *)

let comparison_decl (name:string) (tag:decl_kind) (s:sort) : func_decl =
  { decl_name = name; domain = [s; s]; range = bool_sort; interp = Some tag; int_params = [] }

(* `a <= b` and `a >= b` for a numeric equality `a = b`. *)
let bounds (e:expr) : option (expr & expr) =
  match LA.comparison e with
  | Some (LA.Eq, a, b) ->
    let s = get_sort a in
    Some (App (comparison_decl "<=" op_arith_le s) [a; b],
          App (comparison_decl ">=" op_arith_ge s) [a; b])
  | _ -> None

let triangle (e le ge:expr) : expr =
  let args = [e; App AR.not_decl [le]; App AR.not_decl [ge]] in
  App (B.connective_decl B.Disjunction args) args

let certified (facts:list expr) (e:expr) (lower upper:list LA.coefficient) : bool =
  match bounds e with
  | Some (le, ge) ->
    LA.check lower le facts && LA.check upper ge facts && AR.triangle_equality (triangle e le ge)
  | None -> false

let implied_model (i:interpretation value) : prop =
  (exists (nu:value -> FStar.Real.real). LE.numeric_model i nu) /\
  OE.boolean_model i /\ eq_sound i /\ and_sound i /\ or_sound i /\
  not_sound i /\ true_sound i /\ false_sound i

let lemma_certified (i:interpretation value) (rho:env value) (facts:list expr) (e:expr)
                    (lower upper:list LA.coefficient)
  : Lemma (requires implied_model i /\ conj_holds i rho facts /\ certified facts e lower upper)
          (ensures lit_true i rho e) =
  let Some (le, ge) = bounds e in
  LE.lemma_check_with_numeric_model lower le facts i rho;
  LE.lemma_check_with_numeric_model upper ge facts i rho;
  let t = triangle e le ge in
  AR.lemma_triangle_with_numeric_model t i rho;
  let nle = App AR.not_decl [le] in
  let nge = App AR.not_decl [ge] in
  assert (eval i nle rho == VBool true <==> eval i le rho == VBool false);
  assert (eval i nge rho == VBool true <==> eval i ge rho == VBool false);
  assert (clause_holds i rho [e; nle; nge] <==>
          (lit_true i rho e \/ lit_true i rho nle \/ lit_true i rho nge))

(* ----------------------------------------------------------------- *)
(* Untrusted coefficient search                                        *)
(* ----------------------------------------------------------------- *)

(* Rationals with a positive denominator by construction at run time. *)
type q = { num:int; den:int }

let qzero : q = { num = 0; den = 1 }
let qone : q = { num = 1; den = 1 }

let abs_int (x:int) : nat = if x >= 0 then x else -x

let rec gcd (a b:nat) : Tot nat (decreases b) =
  if b = 0 then a else gcd b (a % b)

let qmake (n d:int) : q =
  if d = 0 then qzero
  else
    let n, d = if d < 0 then -n, -d else n, d in
    let g = gcd (abs_int n) (abs_int d) in
    if g = 0 then qzero else { num = n / g; den = d / g }

let qadd (x y:q) : q = qmake (x.num * y.den + y.num * x.den) (x.den * y.den)
let qmul (x y:q) : q = qmake (x.num * y.num) (x.den * y.den)
let qneg (x:q) : q = { x with num = -x.num }
let qsub (x y:q) : q = qadd x (qneg y)
let qdiv (x y:q) : q = if y.num = 0 then qzero else qmake (x.num * y.den) (x.den * y.num)
let qpositive (x:q) : bool = x.num > 0
let qnegative (x:q) : bool = x.num < 0
let qlt (x y:q) : bool = qnegative (qsub x y)
let qint (n:int) : q = { num = n; den = 1 }

let rec nth_or (#a:Type) (d:a) (xs:list a) (n:nat) : Tot a (decreases xs) =
  match xs with
  | [] -> d
  | x :: rest -> if n = 0 then x else nth_or d rest (n - 1)

let rec map2 (#a #b #c:Type) (f:a -> b -> c) (xs:list a) (ys:list b)
  : Tot (list c) (decreases xs) =
  match xs, ys with
  | x :: xs', y :: ys' -> f x y :: map2 f xs' ys'
  | _, _ -> []

let rec mapi_from (#a #b:Type) (f:nat -> a -> b) (k:nat) (xs:list a)
  : Tot (list b) (decreases xs) =
  match xs with
  | [] -> []
  | x :: rest -> f k x :: mapi_from f (k + 1) rest

let mapi (#a #b:Type) (f:nat -> a -> b) (xs:list a) : list b = mapi_from f 0 xs

let rec replicate (#a:Type) (n:nat) (x:a) : Tot (list a) (decreases n) =
  if n = 0 then [] else x :: replicate (n - 1) x

let rec range_from (k n:nat) : Tot (list nat) (decreases n) =
  if n = 0 then [] else k :: range_from (k + 1) (n - 1)

(* A row `r` with entry `r[c] <> 0` scaled to a unit pivot entry, and the
   elimination of column `c` from another row. *)
let normalize_row (row:list q) (c:nat) : list q =
  let p = nth_or qzero row c in
  L.map (fun x -> qdiv x p) row

let eliminate_column (pivot:list q) (c:nat) (row:list q) : list q =
  let k = nth_or qzero row c in
  if k.num = 0 then row else map2 (fun x y -> qsub x (qmul k y)) row pivot

noeq
type tableau = {
  rows: list (list q);   (* each row: coefficients of all columns, then rhs *)
  basis: list nat;       (* basic column of each row *)
  obj: list q;           (* reduced costs, then minus the objective value *)
  width: nat;            (* number of columns, excluding rhs *)
}

let rec first_negative (xs:list q) (k limit:nat) : Tot (option nat) (decreases xs) =
  match xs with
  | [] -> None
  | x :: rest ->
    if k >= limit then None
    else if qnegative x then Some k
    else first_negative rest (k + 1) limit

(* Bland's rule: minimum ratio, ties broken by the smallest basic column. *)
let rec leaving (rows:list (list q)) (basis:list nat) (c width:nat) (k:nat)
                (best:option (nat & q & nat))
  : Tot (option (nat & q & nat)) (decreases rows) =
  match rows, basis with
  | row :: rest, b :: bs ->
    let a = nth_or qzero row c in
    let best =
      if qpositive a then
        let ratio = qdiv (nth_or qzero row width) a in
        match best with
        | None -> Some (k, ratio, b)
        | Some (_, r, bb) ->
          if qlt ratio r || (ratio = r && b < bb) then Some (k, ratio, b) else best
      else best in
    leaving rest bs c width (k + 1) best
  | _, _ -> best

let pivot (t:tableau) (r c:nat) : tableau =
  let pr = normalize_row (nth_or [] t.rows r) c in
  let rows = mapi (fun i row -> if i = r then pr else eliminate_column pr c row) t.rows in
  let basis = mapi (fun i b -> if i = r then c else b) t.basis in
  { t with rows = rows; basis = basis; obj = eliminate_column pr c t.obj }

let rec simplex (fuel:nat) (t:tableau) : Tot (option tableau) (decreases fuel) =
  if fuel = 0 then None
  else match first_negative t.obj 0 t.width with
  | None -> Some t
  | Some c ->
    (match leaving t.rows t.basis c t.width 0 None with
     | None -> None
     | Some (r, _, _) -> simplex (fuel - 1) (pivot t r c))

let rec column_value (rows:list (list q)) (basis:list nat) (c width:nat)
  : Tot q (decreases rows) =
  match rows, basis with
  | row :: rest, b :: bs -> if b = c then nth_or qzero row width else column_value rest bs c width
  | _, _ -> qzero

let rec sum_rows (rows:list (list q)) (acc:list q) : Tot (list q) (decreases rows) =
  match rows with
  | [] -> acc
  | row :: rest -> sum_rows rest (map2 qadd acc row)

(* Feasibility of `A x = b, x >= 0` (phase one of the simplex method with
   one artificial column per row). `a` lists the rows of `A` over `n`
   columns; `b` gives one entry per row. Returns a feasible `x`. *)
let feasible (a:list (list q)) (b:list q) (n:nat) : option (list q) =
  let m = L.length a in
  let width = n + m in
  let rows = mapi (fun i (row, rhs) ->
      let row, rhs = if qnegative rhs then L.map qneg row, qneg rhs else row, rhs in
      L.append row (L.append (L.map (fun j -> if j = i then qone else qzero) (range_from 0 m)) [rhs]))
    (map2 (fun x y -> (x, y)) a b) in
  if L.length rows <> m then None
  else
    let row_sums = sum_rows rows (replicate (width + 1) qzero) in
    let obj = mapi (fun j x -> if j >= n && j < width then qzero else qneg x) row_sums in
    let t = { rows = rows; basis = range_from n m; obj = obj; width = width } in
    match simplex (20 * (width + 1) + 100) t with
    | None -> None
    | Some t ->
      if (nth_or qone t.obj width).num <> 0 then None
      else Some (L.map (fun c -> column_value t.rows t.basis c width) (range_from 0 n))

(* One prepared assumption: its unit contribution, and whether its weight
   may be negative (equalities). Unusable literals get weight zero. *)
noeq
type row_view = {
  usable: bool;
  equality: bool;
  monomials: list (int & expr);
  constant: int;
  denominator: int;
}

let unusable : row_view =
  { usable = false; equality = false; monomials = []; constant = 0; denominator = 1 }

let view_assumption (lit:bool & expr) : row_view =
  let positive, e = lit in
  match LA.literal 16 positive e with
  | None -> unusable
  | Some (p, r, _, _) ->
    if r = LA.Eq && not p then unusable
    else match LA.prepare_literal (1, 1) positive e with
    | None -> unusable
    | Some c ->
      { usable = true; equality = (r = LA.Eq);
        monomials = P.collect c.P.poly.P.mono [];
        constant = c.P.poly.P.cst; denominator = c.P.poly.P.denom }

let rec add_atoms (ms:list (int & expr)) (atoms:list expr) : Tot (list expr) (decreases ms) =
  match ms with
  | [] -> atoms
  | (c, v) :: rest ->
    add_atoms rest (if c = 0 || L.mem v atoms then atoms else L.append atoms [v])

let rec all_atoms (views:list row_view) (atoms:list expr) : Tot (list expr) (decreases views) =
  match views with
  | [] -> atoms
  | v :: rest -> all_atoms rest (add_atoms v.monomials atoms)

let rec coefficient_of (v:expr) (ms:list (int & expr)) : Tot int (decreases ms) =
  match ms with
  | [] -> 0
  | (c, w) :: rest -> if v = w then c + coefficient_of v rest else coefficient_of v rest

(* LP columns: (assumption index, sign). *)
let rec columns (views:list row_view) (k:nat) : Tot (list (nat & int)) (decreases views) =
  match views with
  | [] -> []
  | v :: rest ->
    let tail = columns rest (k + 1) in
    if not v.usable then tail
    else if v.equality then (k, 1) :: (k, -1) :: tail
    else (k, 1) :: tail

let rec weight_of (k:nat) (cols:list (nat & int)) (xs:list q) : Tot q (decreases cols) =
  match cols, xs with
  | (j, s) :: rest, x :: xs' ->
    let w = weight_of k rest xs' in
    if j = k then (if s > 0 then qadd w x else qsub w x) else w
  | _, _ -> qzero

let rec lcm_denominators (ws:list q) (acc:pos) : Tot pos (decreases ws) =
  match ws with
  | [] -> acc
  | w :: rest ->
    let g = gcd acc (abs_int w.den) in
    let next = if g = 0 then acc else (acc * abs_int w.den) / g in
    lcm_denominators rest (if next > 0 then next else acc)

let integer_weight (scale:pos) (w:q) : LA.coefficient =
  if w.den = 0 then (0, 1) else ((w.num * scale) / w.den, 1)

let max_columns : nat = 128

let search (lits:list (bool & expr)) : option (list LA.coefficient) =
  let views = L.map view_assumption lits in
  let cols = columns views 0 in
  let n = L.length cols in
  if n = 0 || n > max_columns then None
  else
    let atoms = all_atoms views [] in
    if L.length atoms > max_columns then None
    else
      let entry (v:row_view) (s:int) (x:int) : q = qint (s * x) in
      let row_of (atom:expr) : list q =
        L.map (fun (k, s) -> let v = nth_or unusable views k in
                             entry v s (coefficient_of atom v.monomials)) cols in
      let constant_row = L.map (fun (k, s) -> let v = nth_or unusable views k in
                                              entry v s v.constant) cols in
      let a = L.append (L.map row_of atoms) [constant_row] in
      let b = L.append (replicate (L.length atoms) qzero) [qone] in
      match feasible a b n with
      | None -> None
      | Some xs ->
        (* The kernel sums contributions cross-multiplied by the other rows'
           denominators; dividing by each own denominator compensates. *)
        let ws = mapi (fun k (v:row_view) ->
            qmul (weight_of k cols xs) (qint v.denominator)) views in
        let scale = lcm_denominators ws 1 in
        Some (L.map (integer_weight scale) ws)

let candidates (facts:list expr) (e:expr) : option (list LA.coefficient & list LA.coefficient) =
  match bounds e with
  | None -> None
  | Some (le, ge) ->
    match search (LA.assumptions le facts) with
    | None -> None
    | Some lower ->
      match search (LA.assumptions ge facts) with
      | None -> None
      | Some upper -> Some (lower, upper)

let implied_equality (facts:list expr) (e:expr) : bool =
  match candidates facts e with
  | Some (lower, upper) -> certified facts e lower upper
  | None -> false

let lemma_implied_equality (i:interpretation value) (rho:env value) (facts:list expr) (e:expr)
  : Lemma (requires implied_model i /\ conj_holds i rho facts /\ implied_equality facts e)
          (ensures lit_true i rho e) =
  let Some (lower, upper) = candidates facts e in
  lemma_certified i rho facts e lower upper

(* The clausal form `(or (= a b) (not l) (not u))` of the same inference,
   where `l` and `u` imply `a = b` (for example, bounds of either orientation). *)
let implied_clause (e:expr) : bool =
  match e with
  | App f [eq; App nl [l]; App nu [u]] ->
    f.decl_name = "or" && nl.decl_name = "not" && nu.decl_name = "not" &&
    get_sort l = bool_sort && get_sort u = bool_sort &&
    implied_equality [l; u] eq
  | _ -> false

let lemma_implied_clause (i:interpretation value) (rho:env value) (e:expr)
  : Lemma (requires implied_model i /\ implied_clause e)
          (ensures lit_true i rho e) =
  match e with
  | App f [eq; App nl [l]; App nu [u]] ->
    let both () : Lemma (requires lit_true i rho l /\ lit_true i rho u)
                        (ensures lit_true i rho eq) =
      lemma_implied_equality i rho [l; u] eq in
    FStar.Classical.move_requires both ();
    assert (clause_holds i rho [eq; App nl [l]; App nu [u]] <==>
            (lit_true i rho eq \/ lit_true i rho (App nl [l]) \/ lit_true i rho (App nu [u])))
