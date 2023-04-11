
type nat =
| O
| S of nat

val fst : ('a1,'a2) -> 'a1

val snd : ('a1,'a2) -> 'a2

val app : 'a1 ([]) -> 'a1 ([]) -> 'a1 ([])

val max : nat -> nat -> nat

val eqb : Prelude.Bool -> Prelude.Bool -> Prelude.Bool

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos :
 sig
  val eqb : positive -> positive -> Prelude.Bool
 end

val map : ('a1 -> 'a2) -> 'a1 ([]) -> 'a2 ([])

val flat_map : ('a1 -> 'a2 ([])) -> 'a1 ([]) -> 'a2 ([])

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 ([]) -> 'a1

val forallb : ('a1 -> Prelude.Bool) -> 'a1 ([]) -> Prelude.Bool

val filter : ('a1 -> Prelude.Bool) -> 'a1 ([]) -> 'a1 ([])

val split : ('a1,'a2) ([]) -> 'a1 ([]),'a2 ([])

val list_max : nat ([]) -> nat

module Z :
 sig
  val eqb : z -> z -> Prelude.Bool
 end

type ascii =
| Ascii of Prelude.Bool * Prelude.Bool * Prelude.Bool * Prelude.Bool
   * Prelude.Bool * Prelude.Bool * Prelude.Bool * Prelude.Bool

val eqb0 : ascii -> ascii -> Prelude.Bool

type string =
| EmptyString
| String of ascii * string

val eqb1 : string -> string -> Prelude.Bool

val append : string -> string -> string

val length : string -> nat

type 'a has_eqb = 'a -> 'a -> Prelude.Bool

val eqb2 : 'a1 has_eqb -> 'a1 -> 'a1 -> Prelude.Bool

val eqb_string : string has_eqb

val flat_map_maybe :
  ('a1 -> 'a2 ([]) Prelude.Maybe) -> 'a1 ([]) -> 'a2 ([]) Prelude.Maybe

val inb : 'a1 has_eqb -> 'a1 -> 'a1 ([]) -> Prelude.Bool

val dupb : 'a1 has_eqb -> 'a1 ([]) -> Prelude.Bool

val nodupb : 'a1 has_eqb -> 'a1 ([]) -> 'a1 ([])

val eqb_list : 'a1 has_eqb -> 'a1 ([]) has_eqb

type set = string ([])

val mem : string -> set -> Prelude.Bool

val diff : set -> set -> set

val disjointb : set -> set -> Prelude.Bool

val dollars : nat -> string

val fresh : string ([]) -> string

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

val eqb_real : real has_eqb

type type0 =
| Void
| Qunit
| Superpos of type0 * type0
| Joint of type0 * type0

val eqb_type : type0 has_eqb

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

module Variables :
 sig
  val x : string
 end

val bit : type0

val eqb_pair : 'a1 has_eqb -> 'a2 has_eqb -> ('a1,'a2) has_eqb

module Eqb :
 sig
  val eqb_expr : expr -> expr -> Prelude.Bool

  val eqb_prog : prog -> prog -> Prelude.Bool
 end

val eqb_expr0 : expr has_eqb

type context = (string,type0) ([])

val dom : context -> set

val context_find : context -> string -> type0 Prelude.Maybe

val restriction : context -> set -> context

val well_formed_check : context -> Prelude.Bool

val merge : context -> context -> context Prelude.Maybe

val remove : string -> context -> (type0 Prelude.Maybe,context) Prelude.Maybe

val eqb_option : 'a1 has_eqb -> 'a1 Prelude.Maybe has_eqb

val remove_all : context -> context -> context Prelude.Maybe

val inclusionb : context -> context -> Prelude.Bool

val free_vars : expr -> set

val split_sum_list :
  type0 -> type0 -> expr ([]) -> (expr ([]),expr ([])) Prelude.Maybe

val add_to_qpair_list :
  expr -> expr -> (expr,expr ([])) ([]) -> (expr,expr ([])) ([])

val spread_qpair_list : expr ([]) -> (expr,expr ([])) ([]) Prelude.Maybe

val missing_span :
  type0 -> expr ([]) -> string ([]) -> expr ([]) Prelude.Maybe

val span_list : type0 -> expr ([]) -> string ([]) -> expr ([]) Prelude.Maybe

val ortho_check : type0 -> expr ([]) -> Prelude.Bool

val dephase : type0 -> expr -> expr ([])

val split_qpair_list : expr ([]) -> (expr ([]),expr ([])) Prelude.Maybe

val erases_check : string -> type0 -> expr ([]) -> Prelude.Bool

val partition_context : set -> context -> context,context

val partition_pair_context :
  set -> set -> context -> ((context,context),context) Prelude.Maybe

module Checks :
 sig
  val pattern_type_check :
    (context -> context -> expr -> type0 Prelude.Maybe) -> (context -> type0
    -> expr -> context Prelude.Maybe) -> context -> context -> type0 -> type0
    -> (expr,expr) -> Prelude.Bool

  val mixed_type_check :
    (context -> context -> expr -> type0 Prelude.Maybe) -> (prog -> prog_type
    Prelude.Maybe) -> context -> expr -> type0 Prelude.Maybe

  val first_pattern_context_check :
    (context -> type0 -> expr -> context Prelude.Maybe) -> context -> type0
    -> type0 -> expr -> expr -> context Prelude.Maybe

  val mixed_context_check :
    (context -> type0 -> expr -> context Prelude.Maybe) -> (prog -> prog_type
    Prelude.Maybe) -> type0 -> expr -> context Prelude.Maybe

  val pure_type_check : context -> context -> expr -> type0 Prelude.Maybe

  val context_check : context -> type0 -> expr -> context Prelude.Maybe

  val prog_type_check : prog -> prog_type Prelude.Maybe
 end

val mixed_type_check0 : context -> expr -> type0 Prelude.Maybe
