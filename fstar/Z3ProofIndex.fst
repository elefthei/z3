module Z3ProofIndex

let bind_opt (#a #b:Type) (x:option a) (f:a -> option b) : option b =
  match x with Some y -> f y | None -> None

let ( >>= ) = bind_opt

let rec opt_map (#a #b:Type) (f:a -> option b) (xs:list a)
  : Tot (option (list b)) (decreases xs) =
  match xs with
  | [] -> Some []
  | x :: rest ->
    (match f x, opt_map f rest with
     | Some y, Some ys -> Some (y :: ys)
     | _, _ -> None)

(* Persistent maps keyed by naturals, as complete 4-ary tries: key 0 is the
   root value and key k > 0 continues in child ((k - 1) % 4) with key
   (k - 1) / 4. The shallower radix halves the unbounded-integer operations
   and pointer chasing of a binary trie on million-entry proof caches. *)
noeq
type index_tree (a:Type) =
  | Empty : index_tree a
  | Branch : option a -> index_tree a -> index_tree a -> index_tree a -> index_tree a ->
             index_tree a

let rec index_get (#a:Type) (tree:index_tree a) (key:nat)
  : Tot (option a) (decreases key) =
  match tree with
  | Empty -> None
  | Branch value c0 c1 c2 c3 ->
    if key < 1 then value
    else
      let digit = (key - 1) % 4 in
      let rest = (key - 1) / 4 in
      if digit < 2 then (if digit < 1 then index_get c0 rest else index_get c1 rest)
      else if digit < 3 then index_get c2 rest
      else index_get c3 rest

let rec index_put (#a:Type) (tree:index_tree a) (key:nat) (value:a)
  : Tot (index_tree a) (decreases key) =
  match tree with
  | Empty ->
    if key < 1 then Branch (Some value) Empty Empty Empty Empty
    else
      let digit = (key - 1) % 4 in
      let rest = (key - 1) / 4 in
      if digit < 2 then
        (if digit < 1 then Branch None (index_put Empty rest value) Empty Empty Empty
         else Branch None Empty (index_put Empty rest value) Empty Empty)
      else if digit < 3 then Branch None Empty Empty (index_put Empty rest value) Empty
      else Branch None Empty Empty Empty (index_put Empty rest value)
  | Branch old c0 c1 c2 c3 ->
    if key < 1 then Branch (Some value) c0 c1 c2 c3
    else
      let digit = (key - 1) % 4 in
      let rest = (key - 1) / 4 in
      if digit < 2 then
        (if digit < 1 then Branch old (index_put c0 rest value) c1 c2 c3
         else Branch old c0 (index_put c1 rest value) c2 c3)
      else if digit < 3 then Branch old c0 c1 (index_put c2 rest value) c3
      else Branch old c0 c1 c2 (index_put c3 rest value)

let index_find (#a:Type) (tree:index_tree a) (key:int) : option a =
  if key < 0 then None else index_get tree key

let child (#a:Type) (tree:index_tree a) (digit:nat) : index_tree a =
  match tree with
  | Empty -> Empty
  | Branch _ c0 c1 c2 c3 ->
    if digit < 2 then (if digit < 1 then c0 else c1)
    else if digit < 3 then c2 else c3

let lemma_index_get_child (#a:Type) (tree:index_tree a) (key:nat)
  : Lemma (requires key > 0)
          (ensures index_get tree key == index_get (child tree ((key - 1) % 4)) ((key - 1) / 4))
  = match tree with Empty -> () | Branch _ _ _ _ _ -> ()

let lemma_index_put_child (#a:Type) (tree:index_tree a) (key:nat) (value:a) (digit:nat)
  : Lemma (requires key > 0 /\ digit < 4)
          (ensures child (index_put tree key value) digit ==
                   (if digit = (key - 1) % 4 then index_put (child tree digit) ((key - 1) / 4) value
                    else child tree digit))
  = match tree with Empty -> () | Branch _ _ _ _ _ -> ()

let rec lemma_index_put (#a:Type) (tree:index_tree a) (key:nat) (value:a) (query:nat)
  : Lemma (index_get (index_put tree key value) query ==
           (if query = key then Some value else index_get tree query))
          (decreases key) =
  if key = 0 || query = 0 then
    (match tree with
     | Empty -> if query > 0 then lemma_index_get_child (index_put tree key value) query
     | Branch _ _ _ _ _ -> ())
  else (
    let digit = (query - 1) % 4 in
    lemma_index_get_child (index_put tree key value) query;
    lemma_index_get_child tree query;
    lemma_index_put_child tree key value digit;
    FStar.Math.Lemmas.euclidean_division_definition (key - 1) 4;
    FStar.Math.Lemmas.euclidean_division_definition (query - 1) 4;
    if digit = (key - 1) % 4 then
      lemma_index_put (child tree digit) ((key - 1) / 4) value ((query - 1) / 4))
