
type nat =
| O
| S of nat

(** val fst : ('a1,'a2) -> 'a1 **)

let fst = function
| x0,_ -> x0

(** val snd : ('a1,'a2) -> 'a2 **)

let snd = function
| _,y -> y

(** val app : 'a1 ([]) -> 'a1 ([]) -> 'a1 ([]) **)

let rec app l m =
  match l with
  | ([]) -> m
  | (:) (a, l1) -> (:) (a, (app l1 m))

(** val max : nat -> nat -> nat **)

let rec max n m =
  match n with
  | O -> m
  | S n' -> (match m with
             | O -> n
             | S m' -> S (max n' m'))

(** val eqb : Prelude.Bool -> Prelude.Bool -> Prelude.Bool **)

let eqb b1 b2 =
  match b1 with
  | Prelude.True -> b2
  | Prelude.False ->
    (match b2 with
     | Prelude.True -> Prelude.False
     | Prelude.False -> Prelude.True)

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos =
 struct
  (** val eqb : positive -> positive -> Prelude.Bool **)

  let rec eqb p q =
    match p with
    | XI p0 -> (match q with
                | XI q0 -> eqb p0 q0
                | _ -> Prelude.False)
    | XO p0 -> (match q with
                | XO q0 -> eqb p0 q0
                | _ -> Prelude.False)
    | XH -> (match q with
             | XH -> Prelude.True
             | _ -> Prelude.False)
 end

(** val map : ('a1 -> 'a2) -> 'a1 ([]) -> 'a2 ([]) **)

let rec map f = function
| ([]) -> ([])
| (:) (a, t) -> (:) ((f a), (map f t))

(** val flat_map : ('a1 -> 'a2 ([])) -> 'a1 ([]) -> 'a2 ([]) **)

let rec flat_map f = function
| ([]) -> ([])
| (:) (x0, t) -> app (f x0) (flat_map f t)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 ([]) -> 'a1 **)

let rec fold_right f a0 = function
| ([]) -> a0
| (:) (b, t) -> f b (fold_right f a0 t)

(** val forallb : ('a1 -> Prelude.Bool) -> 'a1 ([]) -> Prelude.Bool **)

let rec forallb f = function
| ([]) -> Prelude.True
| (:) (a, l0) -> (Prelude.&&) (f a) (forallb f l0)

(** val filter : ('a1 -> Prelude.Bool) -> 'a1 ([]) -> 'a1 ([]) **)

let rec filter f = function
| ([]) -> ([])
| (:) (x0, l0) ->
  (match f x0 with
   | Prelude.True -> (:) (x0, (filter f l0))
   | Prelude.False -> filter f l0)

(** val split : ('a1,'a2) ([]) -> 'a1 ([]),'a2 ([]) **)

let rec split = function
| ([]) -> ([]),([])
| (:) (p, tl) ->
  let x0,y = p in
  let left,right = split tl in ((:) (x0, left)),((:) (y, right))

(** val list_max : nat ([]) -> nat **)

let list_max l =
  fold_right max O l

module Z =
 struct
  (** val eqb : z -> z -> Prelude.Bool **)

  let eqb x0 y =
    match x0 with
    | Z0 -> (match y with
             | Z0 -> Prelude.True
             | _ -> Prelude.False)
    | Zpos p -> (match y with
                 | Zpos q -> Pos.eqb p q
                 | _ -> Prelude.False)
    | Zneg p -> (match y with
                 | Zneg q -> Pos.eqb p q
                 | _ -> Prelude.False)
 end

type ascii =
| Ascii of Prelude.Bool * Prelude.Bool * Prelude.Bool * Prelude.Bool
   * Prelude.Bool * Prelude.Bool * Prelude.Bool * Prelude.Bool

(** val eqb0 : ascii -> ascii -> Prelude.Bool **)

let eqb0 a b =
  let Ascii (a0, a1, a2, a3, a4, a5, a6, a7) = a in
  let Ascii (b0, b1, b2, b3, b4, b5, b6, b7) = b in
  (match match match match match match match eqb a0 b0 with
                                       | Prelude.True -> eqb a1 b1
                                       | Prelude.False -> Prelude.False with
                                 | Prelude.True -> eqb a2 b2
                                 | Prelude.False -> Prelude.False with
                           | Prelude.True -> eqb a3 b3
                           | Prelude.False -> Prelude.False with
                     | Prelude.True -> eqb a4 b4
                     | Prelude.False -> Prelude.False with
               | Prelude.True -> eqb a5 b5
               | Prelude.False -> Prelude.False with
         | Prelude.True -> eqb a6 b6
         | Prelude.False -> Prelude.False with
   | Prelude.True -> eqb a7 b7
   | Prelude.False -> Prelude.False)

type string =
| EmptyString
| String of ascii * string

(** val eqb1 : string -> string -> Prelude.Bool **)

let rec eqb1 s1 s2 =
  match s1 with
  | EmptyString ->
    (match s2 with
     | EmptyString -> Prelude.True
     | String (_, _) -> Prelude.False)
  | String (c1, s1') ->
    (match s2 with
     | EmptyString -> Prelude.False
     | String (c2, s2') ->
       (match eqb0 c1 c2 with
        | Prelude.True -> eqb1 s1' s2'
        | Prelude.False -> Prelude.False))

(** val append : string -> string -> string **)

let rec append s1 s2 =
  match s1 with
  | EmptyString -> s2
  | String (c, s1') -> String (c, (append s1' s2))

(** val length : string -> nat **)

let rec length = function
| EmptyString -> O
| String (_, s') -> S (length s')

type 'a has_eqb = 'a -> 'a -> Prelude.Bool

(** val eqb2 : 'a1 has_eqb -> 'a1 -> 'a1 -> Prelude.Bool **)

let eqb2 has_eqb0 =
  has_eqb0

(** val eqb_string : string has_eqb **)

let eqb_string =
  eqb1

(** val flat_map_maybe :
    ('a1 -> 'a2 ([]) Prelude.Maybe) -> 'a1 ([]) -> 'a2 ([]) Prelude.Maybe **)

let rec flat_map_maybe f = function
| ([]) -> Prelude.Just ([])
| (:) (e, l0) ->
  (match f e with
   | Prelude.Just b ->
     (match flat_map_maybe f l0 with
      | Prelude.Just l' -> Prelude.Just (app b l')
      | Prelude.Nothing -> Prelude.Nothing)
   | Prelude.Nothing -> Prelude.Nothing)

(** val inb : 'a1 has_eqb -> 'a1 -> 'a1 ([]) -> Prelude.Bool **)

let rec inb h e = function
| ([]) -> Prelude.False
| (:) (e', l') -> (Prelude.||) (eqb2 h e e') (inb h e l')

(** val dupb : 'a1 has_eqb -> 'a1 ([]) -> Prelude.Bool **)

let rec dupb h = function
| ([]) -> Prelude.False
| (:) (e, l') -> (Prelude.||) (inb h e l') (dupb h l')

(** val nodupb : 'a1 has_eqb -> 'a1 ([]) -> 'a1 ([]) **)

let rec nodupb h = function
| ([]) -> ([])
| (:) (e, l') ->
  (match inb h e l' with
   | Prelude.True -> nodupb h l'
   | Prelude.False -> (:) (e, (nodupb h l')))

(** val eqb_list : 'a1 has_eqb -> 'a1 ([]) has_eqb **)

let rec eqb_list h l l' =
  match l with
  | ([]) -> (match l' with
             | ([]) -> Prelude.True
             | (:) (_, _) -> Prelude.False)
  | (:) (e, l0) ->
    (match l' with
     | ([]) -> Prelude.False
     | (:) (e', l'0) -> (Prelude.&&) (eqb2 h e e') (eqb_list h l0 l'0))

type set = string ([])

(** val mem : string -> set -> Prelude.Bool **)

let rec mem x0 = function
| ([]) -> Prelude.False
| (:) (x', x'0) -> (Prelude.||) (eqb1 x0 x') (mem x0 x'0)

(** val diff : set -> set -> set **)

let rec diff x0 x' =
  match x0 with
  | ([]) -> ([])
  | (:) (x1, x2) ->
    (match mem x1 x' with
     | Prelude.True -> diff x2 x'
     | Prelude.False -> (:) (x1, (diff x2 x')))

(** val disjointb : set -> set -> Prelude.Bool **)

let rec disjointb x0 x' =
  match x0 with
  | ([]) -> Prelude.True
  | (:) (x1, x2) -> (Prelude.&&) (Prelude.not (mem x1 x')) (disjointb x2 x')

(** val dollars : nat -> string **)

let rec dollars = function
| O -> EmptyString
| S n' ->
  append (String ((Ascii (Prelude.False, Prelude.False, Prelude.True,
    Prelude.False, Prelude.False, Prelude.True, Prelude.False,
    Prelude.False)), EmptyString)) (dollars n')

(** val fresh : string ([]) -> string **)

let fresh x0 =
  dollars (S (list_max (map length x0)))

type real =
| Pi
| Euler
| Const of z
| Negate of real
| Plus of real * real
| Times of real * real
| Div of real * real
| Sin of real
| Cos of real
| Tan of real
| Arcsin of real
| Arccos of real
| Arctan of real
| Exp of real
| Ln of real
| Sqrt of real

(** val eqb_real : real has_eqb **)

let rec eqb_real r r' =
  match r with
  | Pi -> (match r' with
           | Pi -> Prelude.True
           | _ -> Prelude.False)
  | Euler -> (match r' with
              | Euler -> Prelude.True
              | _ -> Prelude.False)
  | Const n -> (match r' with
                | Const n' -> Z.eqb n n'
                | _ -> Prelude.False)
  | Negate r1 ->
    (match r' with
     | Negate r1' -> eqb_real r1 r1'
     | _ -> Prelude.False)
  | Plus (r1, r2) ->
    (match r' with
     | Plus (r1', r2') -> (Prelude.&&) (eqb_real r1 r1') (eqb_real r2 r2')
     | _ -> Prelude.False)
  | Times (r1, r2) ->
    (match r' with
     | Times (r1', r2') -> (Prelude.&&) (eqb_real r1 r1') (eqb_real r2 r2')
     | _ -> Prelude.False)
  | Div (r1, r2) ->
    (match r' with
     | Div (r1', r2') -> (Prelude.&&) (eqb_real r1 r1') (eqb_real r2 r2')
     | _ -> Prelude.False)
  | Sin r1 -> (match r' with
               | Sin r1' -> eqb_real r1 r1'
               | _ -> Prelude.False)
  | Cos r1 -> (match r' with
               | Cos r1' -> eqb_real r1 r1'
               | _ -> Prelude.False)
  | Tan r1 -> (match r' with
               | Tan r1' -> eqb_real r1 r1'
               | _ -> Prelude.False)
  | Arcsin r1 ->
    (match r' with
     | Arcsin r1' -> eqb_real r1 r1'
     | _ -> Prelude.False)
  | Arccos r1 ->
    (match r' with
     | Arccos r1' -> eqb_real r1 r1'
     | _ -> Prelude.False)
  | Arctan r1 ->
    (match r' with
     | Arctan r1' -> eqb_real r1 r1'
     | _ -> Prelude.False)
  | Exp r1 -> (match r' with
               | Exp r1' -> eqb_real r1 r1'
               | _ -> Prelude.False)
  | Ln r1 -> (match r' with
              | Ln r1' -> eqb_real r1 r1'
              | _ -> Prelude.False)
  | Sqrt r1 ->
    (match r' with
     | Sqrt r1' -> eqb_real r1 r1'
     | _ -> Prelude.False)

type type0 =
| Void
| Qunit
| Superpos of type0 * type0
| Joint of type0 * type0

(** val eqb_type : type0 has_eqb **)

let rec eqb_type t t' =
  match t with
  | Void -> (match t' with
             | Void -> Prelude.True
             | _ -> Prelude.False)
  | Qunit -> (match t' with
              | Qunit -> Prelude.True
              | _ -> Prelude.False)
  | Superpos (t0, t1) ->
    (match t' with
     | Superpos (t0', t1') -> (Prelude.&&) (eqb_type t0 t0') (eqb_type t1 t1')
     | _ -> Prelude.False)
  | Joint (t0, t1) ->
    (match t' with
     | Joint (t0', t1') -> (Prelude.&&) (eqb_type t0 t0') (eqb_type t1 t1')
     | _ -> Prelude.False)

type prog_type =
| Coherent of type0 * type0
| Channel of type0 * type0

type expr =
| Null
| Var of string
| Qpair of expr * expr
| Ctrl of expr * type0 * (expr,expr) ([]) * type0
| Try of expr * expr
| Apply of prog * expr
and prog =
| U3 of real * real * real
| Left of type0 * type0
| Right of type0 * type0
| Lambda of expr * type0 * expr
| Rphase of type0 * expr * real * real

module Variables =
 struct
  (** val x : string **)

  let x =
    String ((Ascii (Prelude.False, Prelude.False, Prelude.False,
      Prelude.True, Prelude.True, Prelude.True, Prelude.True,
      Prelude.False)), EmptyString)
 end

(** val bit : type0 **)

let bit =
  Superpos (Qunit, Qunit)

(** val eqb_pair : 'a1 has_eqb -> 'a2 has_eqb -> ('a1,'a2) has_eqb **)

let eqb_pair eqb3 eqb4 pat pat0 =
  let e0,e1 = pat in
  let e0',e1' = pat0 in (Prelude.&&) (eqb3 e0 e0') (eqb4 e1 e1')

module Eqb =
 struct
  (** val eqb_expr : expr -> expr -> Prelude.Bool **)

  let rec eqb_expr e e' =
    match e with
    | Null -> (match e' with
               | Null -> Prelude.True
               | _ -> Prelude.False)
    | Var x0 -> (match e' with
                 | Var x' -> eqb1 x0 x'
                 | _ -> Prelude.False)
    | Qpair (e0, e1) ->
      (match e' with
       | Qpair (e0', e1') -> (Prelude.&&) (eqb_expr e0 e0') (eqb_expr e1 e1')
       | _ -> Prelude.False)
    | Ctrl (e0, t0, l, t1) ->
      (match e' with
       | Ctrl (e'0, t0', l', t1') ->
         (Prelude.&&)
           ((Prelude.&&) ((Prelude.&&) (eqb_expr e0 e'0) (eqb_type t0 t0'))
             (eqb_list (eqb_pair eqb_expr eqb_expr) l l')) (eqb_type t1 t1')
       | _ -> Prelude.False)
    | Try (e1, e2) ->
      (match e' with
       | Try (e1', e2') -> (Prelude.&&) (eqb_expr e1 e1') (eqb_expr e2 e2')
       | _ -> Prelude.False)
    | Apply (f, e0) ->
      (match e' with
       | Apply (f', e'0) -> (Prelude.&&) (eqb_prog f f') (eqb_expr e0 e'0)
       | _ -> Prelude.False)

  (** val eqb_prog : prog -> prog -> Prelude.Bool **)

  and eqb_prog f f' =
    match f with
    | U3 (theta, phi, lamda) ->
      (match f' with
       | U3 (theta', phi', lamda') ->
         (Prelude.&&)
           ((Prelude.&&) (eqb_real theta theta') (eqb_real phi phi'))
           (eqb_real lamda lamda')
       | _ -> Prelude.False)
    | Left (t0, t1) ->
      (match f' with
       | Left (t0', t1') -> (Prelude.&&) (eqb_type t0 t0') (eqb_type t1 t1')
       | _ -> Prelude.False)
    | Right (t0, t1) ->
      (match f' with
       | Right (t0', t1') -> (Prelude.&&) (eqb_type t0 t0') (eqb_type t1 t1')
       | _ -> Prelude.False)
    | Lambda (e1, t, e2) ->
      (match f' with
       | Lambda (e1', t', e2') ->
         (Prelude.&&) ((Prelude.&&) (eqb_expr e1 e1') (eqb_type t t'))
           (eqb_expr e2 e2')
       | _ -> Prelude.False)
    | Rphase (t, e, r0, r1) ->
      (match f' with
       | Rphase (t', e', r0', r1') ->
         (Prelude.&&)
           ((Prelude.&&) ((Prelude.&&) (eqb_type t t') (eqb_expr e e'))
             (eqb_real r0 r0')) (eqb_real r1 r1')
       | _ -> Prelude.False)
 end

(** val eqb_expr0 : expr has_eqb **)

let eqb_expr0 =
  Eqb.eqb_expr

type context = (string,type0) ([])

(** val dom : context -> set **)

let dom g =
  map fst g

(** val context_find : context -> string -> type0 Prelude.Maybe **)

let rec context_find g x0 =
  match g with
  | ([]) -> Prelude.Nothing
  | (:) (p, g') ->
    let x',t = p in
    (match eqb2 eqb_string x0 x' with
     | Prelude.True -> Prelude.Just t
     | Prelude.False -> context_find g' x0)

(** val restriction : context -> set -> context **)

let restriction g s =
  filter (fun pat -> let x0,_ = pat in mem x0 s) g

(** val well_formed_check : context -> Prelude.Bool **)

let well_formed_check g =
  Prelude.not (dupb eqb_string (dom g))

(** val merge : context -> context -> context Prelude.Maybe **)

let merge d0 d1 =
  match (Prelude.&&) (well_formed_check d0) (well_formed_check d1) with
  | Prelude.True ->
    let d = nodupb (eqb_pair eqb_string eqb_type) (app d0 d1) in
    (match well_formed_check d with
     | Prelude.True -> Prelude.Just d
     | Prelude.False -> Prelude.Nothing)
  | Prelude.False -> Prelude.Nothing

(** val remove :
    string -> context -> (type0 Prelude.Maybe,context) Prelude.Maybe **)

let rec remove x0 = function
| ([]) -> Prelude.Just (Prelude.Nothing,([]))
| (:) (p, g1) ->
  let x1,t0 = p in
  (match remove x0 g1 with
   | Prelude.Just p0 ->
     let t1,g2 = p0 in
     (match t1 with
      | Prelude.Just _ ->
        (match eqb2 eqb_string x0 x1 with
         | Prelude.True -> Prelude.Nothing
         | Prelude.False ->
           (match context_find g1 x1 with
            | Prelude.Just _ -> Prelude.Nothing
            | Prelude.Nothing -> Prelude.Just (t1,((:) ((x1,t0), g2)))))
      | Prelude.Nothing ->
        (match eqb2 eqb_string x0 x1 with
         | Prelude.True -> Prelude.Just ((Prelude.Just t0),g2)
         | Prelude.False ->
           (match context_find g1 x1 with
            | Prelude.Just _ -> Prelude.Nothing
            | Prelude.Nothing -> Prelude.Just (t1,((:) ((x1,t0), g2))))))
   | Prelude.Nothing -> Prelude.Nothing)

(** val eqb_option : 'a1 has_eqb -> 'a1 Prelude.Maybe has_eqb **)

let eqb_option h o o' =
  match o with
  | Prelude.Just e ->
    (match o' with
     | Prelude.Just e' -> eqb2 h e e'
     | Prelude.Nothing -> Prelude.False)
  | Prelude.Nothing ->
    (match o' with
     | Prelude.Just _ -> Prelude.False
     | Prelude.Nothing -> Prelude.True)

(** val remove_all : context -> context -> context Prelude.Maybe **)

let rec remove_all g d =
  match g with
  | ([]) ->
    (match well_formed_check d with
     | Prelude.True -> Prelude.Just d
     | Prelude.False -> Prelude.Nothing)
  | (:) (p, g1) ->
    let x0,t0 = p in
    (match eqb2 (eqb_option eqb_type) (context_find g1 x0) Prelude.Nothing with
     | Prelude.True ->
       (match remove x0 d with
        | Prelude.Just p0 ->
          let o,d1 = p0 in
          (match o with
           | Prelude.Just t1 ->
             (match eqb2 eqb_type t0 t1 with
              | Prelude.True -> remove_all g1 d1
              | Prelude.False -> Prelude.Nothing)
           | Prelude.Nothing -> remove_all g1 d)
        | Prelude.Nothing -> Prelude.Nothing)
     | Prelude.False -> Prelude.Nothing)

(** val inclusionb : context -> context -> Prelude.Bool **)

let inclusionb g g' =
  (Prelude.&&) ((Prelude.&&) (well_formed_check g) (well_formed_check g'))
    (forallb (fun x0 ->
      eqb2 (eqb_option eqb_type) (context_find g x0) (context_find g' x0))
      (dom g))

(** val free_vars : expr -> set **)

let rec free_vars = function
| Null -> ([])
| Var x0 -> (:) (x0, ([]))
| Qpair (e0, e1) -> app (free_vars e0) (free_vars e1)
| Ctrl (e', _, l, _) ->
  app (free_vars e')
    (flat_map (fun pat ->
      let ej,ej' = pat in diff (free_vars ej') (free_vars ej)) l)
| Try (e0, e1) -> app (free_vars e0) (free_vars e1)
| Apply (_, e') -> free_vars e'

(** val split_sum_list :
    type0 -> type0 -> expr ([]) -> (expr ([]),expr ([])) Prelude.Maybe **)

let rec split_sum_list t0 t1 = function
| ([]) -> Prelude.Just (([]),([]))
| (:) (e, l') ->
  (match e with
   | Apply (f, e1) ->
     (match f with
      | Left (t0', t1') ->
        (match eqb2 eqb_type t0 t0' with
         | Prelude.True ->
           (match eqb2 eqb_type t1 t1' with
            | Prelude.True ->
              (match split_sum_list t0 t1 l' with
               | Prelude.Just p ->
                 let l0,l1 = p in Prelude.Just (((:) (e1, l0)),l1)
               | Prelude.Nothing -> Prelude.Nothing)
            | Prelude.False -> Prelude.Nothing)
         | Prelude.False -> Prelude.Nothing)
      | Right (t0', t1') ->
        (match eqb2 eqb_type t0 t0' with
         | Prelude.True ->
           (match eqb2 eqb_type t1 t1' with
            | Prelude.True ->
              (match split_sum_list t0 t1 l' with
               | Prelude.Just p ->
                 let l0,l1 = p in Prelude.Just (l0,((:) (e1, l1)))
               | Prelude.Nothing -> Prelude.Nothing)
            | Prelude.False -> Prelude.Nothing)
         | Prelude.False -> Prelude.Nothing)
      | _ -> Prelude.Nothing)
   | _ -> Prelude.Nothing)

(** val add_to_qpair_list :
    expr -> expr -> (expr,expr ([])) ([]) -> (expr,expr ([])) ([]) **)

let rec add_to_qpair_list e0 e1 = function
| ([]) -> (:) ((e0,((:) (e1, ([])))), ([]))
| (:) (p, l') ->
  let e0',l1 = p in
  (match eqb2 eqb_expr0 e0 e0' with
   | Prelude.True -> (:) ((e0,((:) (e1, l1))), l')
   | Prelude.False -> (:) ((e0',l1), (add_to_qpair_list e0 e1 l')))

(** val spread_qpair_list :
    expr ([]) -> (expr,expr ([])) ([]) Prelude.Maybe **)

let rec spread_qpair_list = function
| ([]) -> Prelude.Just ([])
| (:) (e, l') ->
  (match e with
   | Qpair (e0, e1) ->
     (match spread_qpair_list l' with
      | Prelude.Just l0 -> Prelude.Just (add_to_qpair_list e0 e1 l0)
      | Prelude.Nothing -> Prelude.Nothing)
   | _ -> Prelude.Nothing)

(** val missing_span :
    type0 -> expr ([]) -> string ([]) -> expr ([]) Prelude.Maybe **)

let rec missing_span t l x0 =
  match t with
  | Void ->
    (match l with
     | ([]) -> Prelude.Just ((:) ((Var (fresh x0)), ([])))
     | (:) (y, l0) ->
       (match y with
        | Var x1 ->
          (match l0 with
           | ([]) ->
             (match mem x1 x0 with
              | Prelude.True -> Prelude.Nothing
              | Prelude.False -> Prelude.Just ([]))
           | (:) (_, _) -> Prelude.Nothing)
        | _ -> Prelude.Nothing))
  | Qunit ->
    (match l with
     | ([]) -> Prelude.Just ((:) ((Var (fresh x0)), ([])))
     | (:) (e, l0) ->
       (match e with
        | Null ->
          (match l0 with
           | ([]) -> Prelude.Just ([])
           | (:) (_, _) -> Prelude.Nothing)
        | Var x1 ->
          (match l0 with
           | ([]) ->
             (match mem x1 x0 with
              | Prelude.True -> Prelude.Nothing
              | Prelude.False -> Prelude.Just ([]))
           | (:) (_, _) -> Prelude.Nothing)
        | _ -> Prelude.Nothing))
  | Superpos (t0, t1) ->
    (match l with
     | ([]) -> Prelude.Just ((:) ((Var (fresh x0)), ([])))
     | (:) (e, l0) ->
       (match e with
        | Var x1 ->
          (match l0 with
           | ([]) ->
             (match mem x1 x0 with
              | Prelude.True -> Prelude.Nothing
              | Prelude.False -> Prelude.Just ([]))
           | (:) (_, _) ->
             (match split_sum_list t0 t1 l with
              | Prelude.Just p ->
                let l1,l2 = p in
                (match missing_span t0 l1 x0 with
                 | Prelude.Just l0' ->
                   (match missing_span t1 l2 x0 with
                    | Prelude.Just l1' ->
                      Prelude.Just
                        (app
                          (map (fun x2 -> Apply ((Left (t0, t1)), x2)) l0')
                          (map (fun x2 -> Apply ((Right (t0, t1)), x2)) l1'))
                    | Prelude.Nothing -> Prelude.Nothing)
                 | Prelude.Nothing -> Prelude.Nothing)
              | Prelude.Nothing -> Prelude.Nothing))
        | _ ->
          (match split_sum_list t0 t1 l with
           | Prelude.Just p ->
             let l1,l2 = p in
             (match missing_span t0 l1 x0 with
              | Prelude.Just l0' ->
                (match missing_span t1 l2 x0 with
                 | Prelude.Just l1' ->
                   Prelude.Just
                     (app (map (fun x1 -> Apply ((Left (t0, t1)), x1)) l0')
                       (map (fun x1 -> Apply ((Right (t0, t1)), x1)) l1'))
                 | Prelude.Nothing -> Prelude.Nothing)
              | Prelude.Nothing -> Prelude.Nothing)
           | Prelude.Nothing -> Prelude.Nothing)))
  | Joint (t0, t1) ->
    (match l with
     | ([]) -> Prelude.Just ((:) ((Var (fresh x0)), ([])))
     | (:) (e, l0) ->
       (match e with
        | Var x1 ->
          (match l0 with
           | ([]) ->
             (match mem x1 x0 with
              | Prelude.True -> Prelude.Nothing
              | Prelude.False -> Prelude.Just ([]))
           | (:) (_, _) ->
             (match spread_qpair_list l with
              | Prelude.Just l' ->
                (match missing_span t0 (map fst l')
                         (app x0 (flat_map free_vars (flat_map snd l'))) with
                 | Prelude.Just l1 ->
                   flat_map_maybe (fun pat ->
                     let e0,l2 = pat in
                     (match missing_span t1 l2 (app x0 (free_vars e0)) with
                      | Prelude.Just l1' ->
                        Prelude.Just (map (fun x2 -> Qpair (e0, x2)) l1')
                      | Prelude.Nothing -> Prelude.Nothing))
                     (app (map (fun e0 -> e0,([])) l1) l')
                 | Prelude.Nothing -> Prelude.Nothing)
              | Prelude.Nothing -> Prelude.Nothing))
        | _ ->
          (match spread_qpair_list l with
           | Prelude.Just l' ->
             (match missing_span t0 (map fst l')
                      (app x0 (flat_map free_vars (flat_map snd l'))) with
              | Prelude.Just l1 ->
                flat_map_maybe (fun pat ->
                  let e0,l2 = pat in
                  (match missing_span t1 l2 (app x0 (free_vars e0)) with
                   | Prelude.Just l1' ->
                     Prelude.Just (map (fun x1 -> Qpair (e0, x1)) l1')
                   | Prelude.Nothing -> Prelude.Nothing))
                  (app (map (fun e0 -> e0,([])) l1) l')
              | Prelude.Nothing -> Prelude.Nothing)
           | Prelude.Nothing -> Prelude.Nothing)))

(** val span_list :
    type0 -> expr ([]) -> string ([]) -> expr ([]) Prelude.Maybe **)

let span_list t l x0 =
  match missing_span t l x0 with
  | Prelude.Just l' -> Prelude.Just (app l' l)
  | Prelude.Nothing -> Prelude.Nothing

(** val ortho_check : type0 -> expr ([]) -> Prelude.Bool **)

let ortho_check t l =
  match span_list t l ([]) with
  | Prelude.Just _ -> Prelude.True
  | Prelude.Nothing -> Prelude.False

(** val dephase : type0 -> expr -> expr ([]) **)

let rec dephase t e = match e with
| Ctrl (_, _, l, t') ->
  (match eqb2 eqb_type t t' with
   | Prelude.True -> flat_map (fun pat -> let _,ej' = pat in dephase t ej') l
   | Prelude.False -> (:) (e, ([])))
| Apply (f, e') ->
  (match f with
   | Rphase (t', e0, gamma, gamma') ->
     (match e0 with
      | Var x0 ->
        (match (Prelude.&&)
                 ((Prelude.&&) (eqb2 eqb_type t t')
                   (eqb2 eqb_string Variables.x x0)) (eqb_real gamma gamma') with
         | Prelude.True -> dephase t e'
         | Prelude.False -> (:) (e, ([])))
      | _ -> (:) (e, ([])))
   | _ -> (:) (e, ([])))
| _ -> (:) (e, ([]))

(** val split_qpair_list :
    expr ([]) -> (expr ([]),expr ([])) Prelude.Maybe **)

let rec split_qpair_list = function
| ([]) -> Prelude.Just (([]),([]))
| (:) (e, l') ->
  (match e with
   | Qpair (e0, e1) ->
     (match split_qpair_list l' with
      | Prelude.Just p ->
        let l0,l1 = p in Prelude.Just (((:) (e0, l0)),((:) (e1, l1)))
      | Prelude.Nothing -> Prelude.Nothing)
   | _ -> Prelude.Nothing)

(** val erases_check : string -> type0 -> expr ([]) -> Prelude.Bool **)

let rec erases_check x0 t l =
  let l' = flat_map (dephase t) l in
  (match forallb (eqb2 eqb_expr0 (Var x0)) l' with
   | Prelude.True -> Prelude.True
   | Prelude.False ->
     (match t with
      | Joint (t0, t1) ->
        (match split_qpair_list l' with
         | Prelude.Just p ->
           let l0,l1 = p in
           (Prelude.||) (erases_check x0 t0 l0) (erases_check x0 t1 l1)
         | Prelude.Nothing -> Prelude.False)
      | _ -> Prelude.False))

(** val partition_context : set -> context -> context,context **)

let rec partition_context x0 = function
| ([]) -> ([]),([])
| (:) (p, g') ->
  let x1,t = p in
  let g0,g1 = partition_context x0 g' in
  (match mem x1 x0 with
   | Prelude.True -> ((:) ((x1,t), g0)),g1
   | Prelude.False -> g0,((:) ((x1,t), g1)))

(** val partition_pair_context :
    set -> set -> context -> ((context,context),context) Prelude.Maybe **)

let rec partition_pair_context x0 x1 = function
| ([]) -> Prelude.Just ((([]),([])),([]))
| (:) (p, dp) ->
  let x2,t = p in
  (match mem x2 x0 with
   | Prelude.True ->
     (match mem x2 x1 with
      | Prelude.True ->
        (match partition_pair_context x0 x1 dp with
         | Prelude.Just p0 ->
           let p1,d1 = p0 in
           let d',d0 = p1 in Prelude.Just ((((:) ((x2,t), d')),d0),d1)
         | Prelude.Nothing -> Prelude.Nothing)
      | Prelude.False ->
        (match partition_pair_context x0 x1 dp with
         | Prelude.Just p0 ->
           let p1,d1 = p0 in
           let d',d0 = p1 in Prelude.Just ((d',((:) ((x2,t), d0))),d1)
         | Prelude.Nothing -> Prelude.Nothing))
   | Prelude.False ->
     (match mem x2 x1 with
      | Prelude.True ->
        (match partition_pair_context x0 x1 dp with
         | Prelude.Just p0 ->
           let p1,d1 = p0 in Prelude.Just (p1,((:) ((x2,t), d1)))
         | Prelude.Nothing -> Prelude.Nothing)
      | Prelude.False -> Prelude.Nothing))

module Checks =
 struct
  (** val pattern_type_check :
      (context -> context -> expr -> type0 Prelude.Maybe) -> (context ->
      type0 -> expr -> context Prelude.Maybe) -> context -> context -> type0
      -> type0 -> (expr,expr) -> Prelude.Bool **)

  let pattern_type_check pure_type_check0 context_check0 g d t t' = function
  | ej,ej' ->
    (match context_check0 ([]) t ej with
     | Prelude.Just gj ->
       eqb2 (eqb_option eqb_type) (pure_type_check0 (app g gj) d ej')
         (Prelude.Just t')
     | Prelude.Nothing -> Prelude.False)

  (** val mixed_type_check :
      (context -> context -> expr -> type0 Prelude.Maybe) -> (prog ->
      prog_type Prelude.Maybe) -> context -> expr -> type0 Prelude.Maybe **)

  let rec mixed_type_check pure_type_check0 prog_type_check0 d e = match e with
  | Null -> pure_type_check0 ([]) d e
  | Var _ -> pure_type_check0 ([]) d e
  | Qpair (e0, e1) ->
    (match well_formed_check d with
     | Prelude.True ->
       (match partition_pair_context (free_vars e0) (free_vars e1) d with
        | Prelude.Just p ->
          let p0,d1 = p in
          let d',d0 = p0 in
          (match mixed_type_check pure_type_check0 prog_type_check0
                   (app d' d0) e0 with
           | Prelude.Just t0 ->
             (match mixed_type_check pure_type_check0 prog_type_check0
                      (app d' d1) e1 with
              | Prelude.Just t1 -> Prelude.Just (Joint (t0, t1))
              | Prelude.Nothing -> Prelude.Nothing)
           | Prelude.Nothing -> Prelude.Nothing)
        | Prelude.Nothing -> Prelude.Nothing)
     | Prelude.False -> Prelude.Nothing)
  | Ctrl (_, _, _, _) -> pure_type_check0 ([]) d e
  | Try (e0, e1) ->
    let d0,d1 = partition_context (free_vars e0) d in
    (match disjointb (dom d0) (dom d1) with
     | Prelude.True ->
       (match mixed_type_check pure_type_check0 prog_type_check0 d0 e0 with
        | Prelude.Just t0 ->
          (match mixed_type_check pure_type_check0 prog_type_check0 d1 e1 with
           | Prelude.Just t1 ->
             (match eqb2 eqb_type t0 t1 with
              | Prelude.True -> Prelude.Just t0
              | Prelude.False -> Prelude.Nothing)
           | Prelude.Nothing -> Prelude.Nothing)
        | Prelude.Nothing -> Prelude.Nothing)
     | Prelude.False -> Prelude.Nothing)
  | Apply (f, e') ->
    (match mixed_type_check pure_type_check0 prog_type_check0 d e' with
     | Prelude.Just t ->
       (match prog_type_check0 f with
        | Prelude.Just p ->
          (match p with
           | Coherent (t0, t1) ->
             (match eqb2 eqb_type t t0 with
              | Prelude.True -> Prelude.Just t1
              | Prelude.False -> Prelude.Nothing)
           | Channel (t0, t1) ->
             (match eqb2 eqb_type t t0 with
              | Prelude.True -> Prelude.Just t1
              | Prelude.False -> Prelude.Nothing))
        | Prelude.Nothing -> Prelude.Nothing)
     | Prelude.Nothing -> Prelude.Nothing)

  (** val first_pattern_context_check :
      (context -> type0 -> expr -> context Prelude.Maybe) -> context -> type0
      -> type0 -> expr -> expr -> context Prelude.Maybe **)

  let first_pattern_context_check context_check0 g t t' ej ej' =
    match context_check0 ([]) t ej with
    | Prelude.Just gj -> context_check0 (app g gj) t' ej'
    | Prelude.Nothing -> Prelude.Nothing

  (** val mixed_context_check :
      (context -> type0 -> expr -> context Prelude.Maybe) -> (prog ->
      prog_type Prelude.Maybe) -> type0 -> expr -> context Prelude.Maybe **)

  let rec mixed_context_check context_check0 prog_type_check0 t e = match e with
  | Null -> context_check0 ([]) t e
  | Var _ -> context_check0 ([]) t e
  | Qpair (e0, e1) ->
    (match t with
     | Joint (t0, t1) ->
       (match mixed_context_check context_check0 prog_type_check0 t0 e0 with
        | Prelude.Just d0 ->
          (match mixed_context_check context_check0 prog_type_check0 t1 e1 with
           | Prelude.Just d1 -> merge d0 d1
           | Prelude.Nothing -> Prelude.Nothing)
        | Prelude.Nothing -> Prelude.Nothing)
     | _ -> Prelude.Nothing)
  | Ctrl (_, _, _, _) -> context_check0 ([]) t e
  | Try (e0, e1) ->
    (match mixed_context_check context_check0 prog_type_check0 t e0 with
     | Prelude.Just d0 ->
       (match mixed_context_check context_check0 prog_type_check0 t e1 with
        | Prelude.Just d1 ->
          (match disjointb (dom d0) (dom d1) with
           | Prelude.True -> Prelude.Just (app d0 d1)
           | Prelude.False -> Prelude.Nothing)
        | Prelude.Nothing -> Prelude.Nothing)
     | Prelude.Nothing -> Prelude.Nothing)
  | Apply (f, e') ->
    (match prog_type_check0 f with
     | Prelude.Just p ->
       (match p with
        | Coherent (t0, t1) ->
          (match eqb2 eqb_type t t1 with
           | Prelude.True ->
             mixed_context_check context_check0 prog_type_check0 t0 e'
           | Prelude.False -> Prelude.Nothing)
        | Channel (t0, t1) ->
          (match eqb2 eqb_type t t1 with
           | Prelude.True ->
             mixed_context_check context_check0 prog_type_check0 t0 e'
           | Prelude.False -> Prelude.Nothing))
     | Prelude.Nothing -> Prelude.Nothing)

  (** val pure_type_check :
      context -> context -> expr -> type0 Prelude.Maybe **)

  let rec pure_type_check g d e =
    let mixed_type_check1 = mixed_type_check pure_type_check prog_type_check
    in
    (match e with
     | Null ->
       (match well_formed_check g with
        | Prelude.True ->
          (match d with
           | ([]) -> Prelude.Just Qunit
           | (:) (_, _) -> Prelude.Nothing)
        | Prelude.False -> Prelude.Nothing)
     | Var x0 ->
       (match well_formed_check g with
        | Prelude.True ->
          (match d with
           | ([]) -> context_find g x0
           | (:) (p, l) ->
             let x',t = p in
             (match l with
              | ([]) ->
                (match eqb2 eqb_string x0 x' with
                 | Prelude.True ->
                   (match context_find g x0 with
                    | Prelude.Just _ -> Prelude.Nothing
                    | Prelude.Nothing -> Prelude.Just t)
                 | Prelude.False -> Prelude.Nothing)
              | (:) (_, _) -> Prelude.Nothing))
        | Prelude.False -> Prelude.Nothing)
     | Qpair (e0, e1) ->
       (match well_formed_check (app g d) with
        | Prelude.True ->
          (match partition_pair_context (free_vars e0) (free_vars e1) d with
           | Prelude.Just p ->
             let p0,d1 = p in
             let d',d0 = p0 in
             (match pure_type_check g (app d' d0) e0 with
              | Prelude.Just t0 ->
                (match pure_type_check g (app d' d1) e1 with
                 | Prelude.Just t1 -> Prelude.Just (Joint (t0, t1))
                 | Prelude.Nothing -> Prelude.Nothing)
              | Prelude.Nothing -> Prelude.Nothing)
           | Prelude.Nothing -> Prelude.Nothing)
        | Prelude.False -> Prelude.Nothing)
     | Ctrl (e0, t, l, t') ->
       let xe = free_vars e0 in
       let d0,d' = partition_context xe d in
       let ej,ej' = split l in
       let g0,g' = partition_context xe g in
       (match (Prelude.&&)
                ((Prelude.&&)
                  ((Prelude.&&)
                    ((Prelude.&&)
                      (well_formed_check (app g0 (app g' (app d0 d'))))
                      (eqb2 (eqb_option eqb_type)
                        (mixed_type_check1 (app g0 d0) e0) (Prelude.Just t)))
                    (ortho_check t ej))
                  (forallb
                    (pattern_type_check pure_type_check context_check
                      (app g0 g') (app d0 d') t t') l))
                (forallb (fun x0 -> erases_check x0 t' ej') (dom d0)) with
        | Prelude.True -> Prelude.Just t'
        | Prelude.False -> Prelude.Nothing)
     | Try (_, _) -> Prelude.Nothing
     | Apply (f, e') ->
       (match pure_type_check g d e' with
        | Prelude.Just t' ->
          (match prog_type_check f with
           | Prelude.Just p ->
             (match p with
              | Coherent (t0, t1) ->
                (match eqb2 eqb_type t' t0 with
                 | Prelude.True -> Prelude.Just t1
                 | Prelude.False -> Prelude.Nothing)
              | Channel (_, _) -> Prelude.Nothing)
           | Prelude.Nothing -> Prelude.Nothing)
        | Prelude.Nothing -> Prelude.Nothing))

  (** val context_check :
      context -> type0 -> expr -> context Prelude.Maybe **)

  and context_check g t e =
    let mixed_context_check0 =
      mixed_context_check context_check prog_type_check
    in
    (match e with
     | Null ->
       (match t with
        | Qunit ->
          (match well_formed_check g with
           | Prelude.True -> Prelude.Just ([])
           | Prelude.False -> Prelude.Nothing)
        | _ -> Prelude.Nothing)
     | Var x0 ->
       (match well_formed_check g with
        | Prelude.True ->
          (match context_find g x0 with
           | Prelude.Just t' ->
             (match eqb2 eqb_type t t' with
              | Prelude.True -> Prelude.Just ([])
              | Prelude.False -> Prelude.Nothing)
           | Prelude.Nothing -> Prelude.Just ((:) ((x0,t), ([]))))
        | Prelude.False -> Prelude.Nothing)
     | Qpair (e0, e1) ->
       (match t with
        | Joint (t0, t1) ->
          (match context_check g t0 e0 with
           | Prelude.Just d0 ->
             (match context_check g t1 e1 with
              | Prelude.Just d1 -> merge d0 d1
              | Prelude.Nothing -> Prelude.Nothing)
           | Prelude.Nothing -> Prelude.Nothing)
        | _ -> Prelude.Nothing)
     | Ctrl (e', t0, l, t1) ->
       let ej,ej' = split l in
       (match eqb2 eqb_type t t1 with
        | Prelude.True ->
          (match mixed_context_check0 t0 e' with
           | Prelude.Just d ->
             (match l with
              | ([]) -> remove_all g d
              | (:) (p, l0) ->
                let e0,e0' = p in
                (match first_pattern_context_check context_check g t0 t1 e0
                         e0' with
                 | Prelude.Just d0 ->
                   (match (Prelude.&&)
                            ((Prelude.&&)
                              ((Prelude.&&) (inclusionb d (app g d0))
                                (ortho_check t0 ej))
                              (forallb
                                (pattern_type_check pure_type_check
                                  context_check g d0 t0 t1) l0))
                            (forallb (fun x0 -> erases_check x0 t1 ej')
                              (dom d)) with
                    | Prelude.True -> Prelude.Just d0
                    | Prelude.False -> Prelude.Nothing)
                 | Prelude.Nothing -> Prelude.Nothing))
           | Prelude.Nothing -> Prelude.Nothing)
        | Prelude.False -> Prelude.Nothing)
     | Try (_, _) -> Prelude.Nothing
     | Apply (f, e') ->
       (match prog_type_check f with
        | Prelude.Just p ->
          (match p with
           | Coherent (t0, t1) ->
             (match eqb2 eqb_type t t1 with
              | Prelude.True -> context_check g t0 e'
              | Prelude.False -> Prelude.Nothing)
           | Channel (_, _) -> Prelude.Nothing)
        | Prelude.Nothing -> Prelude.Nothing))

  (** val prog_type_check : prog -> prog_type Prelude.Maybe **)

  and prog_type_check f =
    let mixed_type_check1 = mixed_type_check pure_type_check prog_type_check
    in
    (match f with
     | U3 (_, _, _) -> Prelude.Just (Coherent (bit, bit))
     | Left (t0, t1) -> Prelude.Just (Coherent (t0, (Superpos (t0, t1))))
     | Right (t0, t1) -> Prelude.Just (Coherent (t1, (Superpos (t0, t1))))
     | Lambda (e, t, e') ->
       (match context_check ([]) t e with
        | Prelude.Just d ->
          (match pure_type_check ([]) d e' with
           | Prelude.Just t' -> Prelude.Just (Coherent (t, t'))
           | Prelude.Nothing ->
             (match mixed_type_check1 (restriction d (free_vars e')) e' with
              | Prelude.Just t' -> Prelude.Just (Channel (t, t'))
              | Prelude.Nothing -> Prelude.Nothing))
        | Prelude.Nothing -> Prelude.Nothing)
     | Rphase (t, e, _, _) ->
       (match context_check ([]) t e with
        | Prelude.Just _ -> Prelude.Just (Coherent (t, t))
        | Prelude.Nothing -> Prelude.Nothing))
 end

(** val mixed_type_check0 : context -> expr -> type0 Prelude.Maybe **)

let mixed_type_check0 =
  Checks.mixed_type_check Checks.pure_type_check Checks.prog_type_check
