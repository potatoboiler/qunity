module Pure_type_check where

import qualified Prelude

data Nat =
   O
 | S Nat

fst :: ((,) a1 a2) -> a1
fst p =
  case p of {
   (,) x0 _ -> x0}

snd :: ((,) a1 a2) -> a2
snd p =
  case p of {
   (,) _ y -> y}

app :: (([]) a1) -> (([]) a1) -> ([]) a1
app l m =
  case l of {
   ([]) -> m;
   (:) a l1 -> (:) a (app l1 m)}

max :: Nat -> Nat -> Nat
max n m =
  case n of {
   O -> m;
   S n' -> case m of {
            O -> n;
            S m' -> S (max n' m')}}

eqb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
eqb b1 b2 =
  case b1 of {
   Prelude.True -> b2;
   Prelude.False ->
    case b2 of {
     Prelude.True -> Prelude.False;
     Prelude.False -> Prelude.True}}

data Positive =
   XI Positive
 | XO Positive
 | XH

data Z =
   Z0
 | Zpos Positive
 | Zneg Positive

eqb0 :: Positive -> Positive -> Prelude.Bool
eqb0 p q =
  case p of {
   XI p0 -> case q of {
             XI q0 -> eqb0 p0 q0;
             _ -> Prelude.False};
   XO p0 -> case q of {
             XO q0 -> eqb0 p0 q0;
             _ -> Prelude.False};
   XH -> case q of {
          XH -> Prelude.True;
          _ -> Prelude.False}}

map :: (a1 -> a2) -> (([]) a1) -> ([]) a2
map f l =
  case l of {
   ([]) -> ([]);
   (:) a t -> (:) (f a) (map f t)}

flat_map :: (a1 -> ([]) a2) -> (([]) a1) -> ([]) a2
flat_map f l =
  case l of {
   ([]) -> ([]);
   (:) x0 t -> app (f x0) (flat_map f t)}

fold_right :: (a2 -> a1 -> a1) -> a1 -> (([]) a2) -> a1
fold_right f a0 l =
  case l of {
   ([]) -> a0;
   (:) b t -> f b (fold_right f a0 t)}

forallb :: (a1 -> Prelude.Bool) -> (([]) a1) -> Prelude.Bool
forallb f l =
  case l of {
   ([]) -> Prelude.True;
   (:) a l0 -> (Prelude.&&) (f a) (forallb f l0)}

filter :: (a1 -> Prelude.Bool) -> (([]) a1) -> ([]) a1
filter f l =
  case l of {
   ([]) -> ([]);
   (:) x0 l0 ->
    case f x0 of {
     Prelude.True -> (:) x0 (filter f l0);
     Prelude.False -> filter f l0}}

split :: (([]) ((,) a1 a2)) -> (,) (([]) a1) (([]) a2)
split l =
  case l of {
   ([]) -> (,) ([]) ([]);
   (:) p tl ->
    case p of {
     (,) x0 y ->
      case split tl of {
       (,) left right -> (,) ((:) x0 left) ((:) y right)}}}

list_max :: (([]) Nat) -> Nat
list_max l =
  fold_right max O l

eqb1 :: Z -> Z -> Prelude.Bool
eqb1 x0 y =
  case x0 of {
   Z0 -> case y of {
          Z0 -> Prelude.True;
          _ -> Prelude.False};
   Zpos p -> case y of {
              Zpos q -> eqb0 p q;
              _ -> Prelude.False};
   Zneg p -> case y of {
              Zneg q -> eqb0 p q;
              _ -> Prelude.False}}

data Ascii0 =
   Ascii Prelude.Bool Prelude.Bool Prelude.Bool Prelude.Bool Prelude.Bool 
 Prelude.Bool Prelude.Bool Prelude.Bool

eqb2 :: Ascii0 -> Ascii0 -> Prelude.Bool
eqb2 a b =
  case a of {
   Ascii a0 a1 a2 a3 a4 a5 a6 a7 ->
    case b of {
     Ascii b0 b1 b2 b3 b4 b5 b6 b7 ->
      case case case case case case case eqb a0 b0 of {
                                     Prelude.True -> eqb a1 b1;
                                     Prelude.False -> Prelude.False} of {
                                Prelude.True -> eqb a2 b2;
                                Prelude.False -> Prelude.False} of {
                           Prelude.True -> eqb a3 b3;
                           Prelude.False -> Prelude.False} of {
                      Prelude.True -> eqb a4 b4;
                      Prelude.False -> Prelude.False} of {
                 Prelude.True -> eqb a5 b5;
                 Prelude.False -> Prelude.False} of {
            Prelude.True -> eqb a6 b6;
            Prelude.False -> Prelude.False} of {
       Prelude.True -> eqb a7 b7;
       Prelude.False -> Prelude.False}}}

data String =
   EmptyString
 | String0 Ascii0 String

eqb3 :: String -> String -> Prelude.Bool
eqb3 s1 s2 =
  case s1 of {
   EmptyString ->
    case s2 of {
     EmptyString -> Prelude.True;
     String0 _ _ -> Prelude.False};
   String0 c1 s1' ->
    case s2 of {
     EmptyString -> Prelude.False;
     String0 c2 s2' ->
      case eqb2 c1 c2 of {
       Prelude.True -> eqb3 s1' s2';
       Prelude.False -> Prelude.False}}}

append :: String -> String -> String
append s1 s2 =
  case s1 of {
   EmptyString -> s2;
   String0 c s1' -> String0 c (append s1' s2)}

length :: String -> Nat
length s =
  case s of {
   EmptyString -> O;
   String0 _ s' -> S (length s')}

type Has_eqb a = a -> a -> Prelude.Bool

eqb4 :: (Has_eqb a1) -> a1 -> a1 -> Prelude.Bool
eqb4 has_eqb =
  has_eqb

eqb_string :: Has_eqb String
eqb_string =
  eqb3

flat_map_maybe :: (a1 -> Prelude.Maybe (([]) a2)) -> (([]) a1) ->
                  Prelude.Maybe (([]) a2)
flat_map_maybe f l =
  case l of {
   ([]) -> Prelude.Just ([]);
   (:) e l0 ->
    case f e of {
     Prelude.Just b ->
      case flat_map_maybe f l0 of {
       Prelude.Just l' -> Prelude.Just (app b l');
       Prelude.Nothing -> Prelude.Nothing};
     Prelude.Nothing -> Prelude.Nothing}}

inb :: (Has_eqb a1) -> a1 -> (([]) a1) -> Prelude.Bool
inb h e l =
  case l of {
   ([]) -> Prelude.False;
   (:) e' l' -> (Prelude.||) (eqb4 h e e') (inb h e l')}

dupb :: (Has_eqb a1) -> (([]) a1) -> Prelude.Bool
dupb h l =
  case l of {
   ([]) -> Prelude.False;
   (:) e l' -> (Prelude.||) (inb h e l') (dupb h l')}

nodupb :: (Has_eqb a1) -> (([]) a1) -> ([]) a1
nodupb h l =
  case l of {
   ([]) -> ([]);
   (:) e l' ->
    case inb h e l' of {
     Prelude.True -> nodupb h l';
     Prelude.False -> (:) e (nodupb h l')}}

eqb_list :: (Has_eqb a1) -> Has_eqb (([]) a1)
eqb_list h l l' =
  case l of {
   ([]) -> case l' of {
            ([]) -> Prelude.True;
            (:) _ _ -> Prelude.False};
   (:) e l0 ->
    case l' of {
     ([]) -> Prelude.False;
     (:) e' l'0 -> (Prelude.&&) (eqb4 h e e') (eqb_list h l0 l'0)}}

type Set = ([]) String

mem :: String -> Set -> Prelude.Bool
mem x0 x1 =
  case x1 of {
   ([]) -> Prelude.False;
   (:) x' x'0 -> (Prelude.||) (eqb3 x0 x') (mem x0 x'0)}

diff :: Set -> Set -> Set
diff x0 x' =
  case x0 of {
   ([]) -> ([]);
   (:) x1 x2 ->
    case mem x1 x' of {
     Prelude.True -> diff x2 x';
     Prelude.False -> (:) x1 (diff x2 x')}}

disjointb :: Set -> Set -> Prelude.Bool
disjointb x0 x' =
  case x0 of {
   ([]) -> Prelude.True;
   (:) x1 x2 -> (Prelude.&&) (Prelude.not (mem x1 x')) (disjointb x2 x')}

dollars :: Nat -> String
dollars n =
  case n of {
   O -> EmptyString;
   S n' ->
    append (String0 (Ascii Prelude.False Prelude.False Prelude.True
      Prelude.False Prelude.False Prelude.True Prelude.False Prelude.False)
      EmptyString) (dollars n')}

fresh :: (([]) String) -> String
fresh x0 =
  dollars (S (list_max (map length x0)))

data Real =
   Pi
 | Euler
 | Const Z
 | Negate Real
 | Plus Real Real
 | Times Real Real
 | Div Real Real
 | Sin Real
 | Cos Real
 | Tan Real
 | Arcsin Real
 | Arccos Real
 | Arctan Real
 | Exp Real
 | Ln Real
 | Sqrt Real

eqb_real :: Has_eqb Real
eqb_real r r' =
  case r of {
   Pi -> case r' of {
          Pi -> Prelude.True;
          _ -> Prelude.False};
   Euler -> case r' of {
             Euler -> Prelude.True;
             _ -> Prelude.False};
   Const n -> case r' of {
               Const n' -> eqb1 n n';
               _ -> Prelude.False};
   Negate r1 ->
    case r' of {
     Negate r1' -> eqb_real r1 r1';
     _ -> Prelude.False};
   Plus r1 r2 ->
    case r' of {
     Plus r1' r2' -> (Prelude.&&) (eqb_real r1 r1') (eqb_real r2 r2');
     _ -> Prelude.False};
   Times r1 r2 ->
    case r' of {
     Times r1' r2' -> (Prelude.&&) (eqb_real r1 r1') (eqb_real r2 r2');
     _ -> Prelude.False};
   Div r1 r2 ->
    case r' of {
     Div r1' r2' -> (Prelude.&&) (eqb_real r1 r1') (eqb_real r2 r2');
     _ -> Prelude.False};
   Sin r1 -> case r' of {
              Sin r1' -> eqb_real r1 r1';
              _ -> Prelude.False};
   Cos r1 -> case r' of {
              Cos r1' -> eqb_real r1 r1';
              _ -> Prelude.False};
   Tan r1 -> case r' of {
              Tan r1' -> eqb_real r1 r1';
              _ -> Prelude.False};
   Arcsin r1 ->
    case r' of {
     Arcsin r1' -> eqb_real r1 r1';
     _ -> Prelude.False};
   Arccos r1 ->
    case r' of {
     Arccos r1' -> eqb_real r1 r1';
     _ -> Prelude.False};
   Arctan r1 ->
    case r' of {
     Arctan r1' -> eqb_real r1 r1';
     _ -> Prelude.False};
   Exp r1 -> case r' of {
              Exp r1' -> eqb_real r1 r1';
              _ -> Prelude.False};
   Ln r1 -> case r' of {
             Ln r1' -> eqb_real r1 r1';
             _ -> Prelude.False};
   Sqrt r1 -> case r' of {
               Sqrt r1' -> eqb_real r1 r1';
               _ -> Prelude.False}}

data Type =
   Void
 | Qunit
 | Superpos Type Type
 | Joint Type Type

eqb_type :: Has_eqb Type
eqb_type t t' =
  case t of {
   Void -> case t' of {
            Void -> Prelude.True;
            _ -> Prelude.False};
   Qunit -> case t' of {
             Qunit -> Prelude.True;
             _ -> Prelude.False};
   Superpos t0 t1 ->
    case t' of {
     Superpos t0' t1' -> (Prelude.&&) (eqb_type t0 t0') (eqb_type t1 t1');
     _ -> Prelude.False};
   Joint t0 t1 ->
    case t' of {
     Joint t0' t1' -> (Prelude.&&) (eqb_type t0 t0') (eqb_type t1 t1');
     _ -> Prelude.False}}

data Prog_type =
   Coherent Type Type
 | Channel Type Type

data Expr =
   Null
 | Var String
 | Qpair Expr Expr
 | Ctrl Expr Type (([]) ((,) Expr Expr)) Type
 | Try Expr Expr
 | Apply Prog Expr
data Prog =
   U3 Real Real Real
 | Left Type Type
 | Right Type Type
 | Lambda Expr Type Expr
 | Rphase Type Expr Real Real

x :: String
x =
  String0 (Ascii Prelude.False Prelude.False Prelude.False Prelude.True
    Prelude.True Prelude.True Prelude.True Prelude.False) EmptyString

bit :: Type
bit =
  Superpos Qunit Qunit

eqb_pair :: (Has_eqb a1) -> (Has_eqb a2) -> Has_eqb ((,) a1 a2)
eqb_pair eqb5 eqb6 pat pat0 =
  case pat of {
   (,) e0 e1 ->
    case pat0 of {
     (,) e0' e1' -> (Prelude.&&) (eqb5 e0 e0') (eqb6 e1 e1')}}

eqb_expr :: Expr -> Expr -> Prelude.Bool
eqb_expr e e' =
  case e of {
   Null -> case e' of {
            Null -> Prelude.True;
            _ -> Prelude.False};
   Var x0 -> case e' of {
              Var x' -> eqb3 x0 x';
              _ -> Prelude.False};
   Qpair e0 e1 ->
    case e' of {
     Qpair e0' e1' -> (Prelude.&&) (eqb_expr e0 e0') (eqb_expr e1 e1');
     _ -> Prelude.False};
   Ctrl e0 t0 l t1 ->
    case e' of {
     Ctrl e'0 t0' l' t1' ->
      (Prelude.&&)
        ((Prelude.&&) ((Prelude.&&) (eqb_expr e0 e'0) (eqb_type t0 t0'))
          (eqb_list (eqb_pair eqb_expr eqb_expr) l l')) (eqb_type t1 t1');
     _ -> Prelude.False};
   Try e1 e2 ->
    case e' of {
     Try e1' e2' -> (Prelude.&&) (eqb_expr e1 e1') (eqb_expr e2 e2');
     _ -> Prelude.False};
   Apply f e0 ->
    case e' of {
     Apply f' e'0 -> (Prelude.&&) (eqb_prog f f') (eqb_expr e0 e'0);
     _ -> Prelude.False}}

eqb_prog :: Prog -> Prog -> Prelude.Bool
eqb_prog f f' =
  case f of {
   U3 theta phi lamda ->
    case f' of {
     U3 theta' phi' lamda' ->
      (Prelude.&&) ((Prelude.&&) (eqb_real theta theta') (eqb_real phi phi'))
        (eqb_real lamda lamda');
     _ -> Prelude.False};
   Left t0 t1 ->
    case f' of {
     Left t0' t1' -> (Prelude.&&) (eqb_type t0 t0') (eqb_type t1 t1');
     _ -> Prelude.False};
   Right t0 t1 ->
    case f' of {
     Right t0' t1' -> (Prelude.&&) (eqb_type t0 t0') (eqb_type t1 t1');
     _ -> Prelude.False};
   Lambda e1 t e2 ->
    case f' of {
     Lambda e1' t' e2' ->
      (Prelude.&&) ((Prelude.&&) (eqb_expr e1 e1') (eqb_type t t'))
        (eqb_expr e2 e2');
     _ -> Prelude.False};
   Rphase t e r0 r1 ->
    case f' of {
     Rphase t' e' r0' r1' ->
      (Prelude.&&)
        ((Prelude.&&) ((Prelude.&&) (eqb_type t t') (eqb_expr e e'))
          (eqb_real r0 r0')) (eqb_real r1 r1');
     _ -> Prelude.False}}

eqb_expr0 :: Has_eqb Expr
eqb_expr0 =
  eqb_expr

type Context = ([]) ((,) String Type)

dom :: Context -> Set
dom g =
  map fst g

context_find :: Context -> String -> Prelude.Maybe Type
context_find g x0 =
  case g of {
   ([]) -> Prelude.Nothing;
   (:) p g' ->
    case p of {
     (,) x' t ->
      case eqb4 eqb_string x0 x' of {
       Prelude.True -> Prelude.Just t;
       Prelude.False -> context_find g' x0}}}

restriction :: Context -> Set -> Context
restriction g s =
  filter (\pat -> case pat of {
                   (,) x0 _ -> mem x0 s}) g

well_formed_check :: Context -> Prelude.Bool
well_formed_check g =
  Prelude.not (dupb eqb_string (dom g))

merge :: Context -> Context -> Prelude.Maybe Context
merge d0 d1 =
  case (Prelude.&&) (well_formed_check d0) (well_formed_check d1) of {
   Prelude.True ->
    let {d = nodupb (eqb_pair eqb_string eqb_type) (app d0 d1)} in
    case well_formed_check d of {
     Prelude.True -> Prelude.Just d;
     Prelude.False -> Prelude.Nothing};
   Prelude.False -> Prelude.Nothing}

remove :: String -> Context -> Prelude.Maybe
          ((,) (Prelude.Maybe Type) Context)
remove x0 g =
  case g of {
   ([]) -> Prelude.Just ((,) Prelude.Nothing ([]));
   (:) p g1 ->
    case p of {
     (,) x1 t0 ->
      case remove x0 g1 of {
       Prelude.Just p0 ->
        case p0 of {
         (,) t1 g2 ->
          case t1 of {
           Prelude.Just _ ->
            case eqb4 eqb_string x0 x1 of {
             Prelude.True -> Prelude.Nothing;
             Prelude.False ->
              case context_find g1 x1 of {
               Prelude.Just _ -> Prelude.Nothing;
               Prelude.Nothing -> Prelude.Just ((,) t1 ((:) ((,) x1 t0) g2))}};
           Prelude.Nothing ->
            case eqb4 eqb_string x0 x1 of {
             Prelude.True -> Prelude.Just ((,) (Prelude.Just t0) g2);
             Prelude.False ->
              case context_find g1 x1 of {
               Prelude.Just _ -> Prelude.Nothing;
               Prelude.Nothing -> Prelude.Just ((,) t1 ((:) ((,) x1 t0) g2))}}}};
       Prelude.Nothing -> Prelude.Nothing}}}

eqb_option :: (Has_eqb a1) -> Has_eqb (Prelude.Maybe a1)
eqb_option h o o' =
  case o of {
   Prelude.Just e ->
    case o' of {
     Prelude.Just e' -> eqb4 h e e';
     Prelude.Nothing -> Prelude.False};
   Prelude.Nothing ->
    case o' of {
     Prelude.Just _ -> Prelude.False;
     Prelude.Nothing -> Prelude.True}}

remove_all :: Context -> Context -> Prelude.Maybe Context
remove_all g d =
  case g of {
   ([]) ->
    case well_formed_check d of {
     Prelude.True -> Prelude.Just d;
     Prelude.False -> Prelude.Nothing};
   (:) p g1 ->
    case p of {
     (,) x0 t0 ->
      case eqb4 (eqb_option eqb_type) (context_find g1 x0) Prelude.Nothing of {
       Prelude.True ->
        case remove x0 d of {
         Prelude.Just p0 ->
          case p0 of {
           (,) o d1 ->
            case o of {
             Prelude.Just t1 ->
              case eqb4 eqb_type t0 t1 of {
               Prelude.True -> remove_all g1 d1;
               Prelude.False -> Prelude.Nothing};
             Prelude.Nothing -> remove_all g1 d}};
         Prelude.Nothing -> Prelude.Nothing};
       Prelude.False -> Prelude.Nothing}}}

inclusionb :: Context -> Context -> Prelude.Bool
inclusionb g g' =
  (Prelude.&&) ((Prelude.&&) (well_formed_check g) (well_formed_check g'))
    (forallb (\x0 ->
      eqb4 (eqb_option eqb_type) (context_find g x0) (context_find g' x0))
      (dom g))

free_vars :: Expr -> Set
free_vars e =
  case e of {
   Null -> ([]);
   Var x0 -> (:) x0 ([]);
   Qpair e0 e1 -> app (free_vars e0) (free_vars e1);
   Ctrl e' _ l _ ->
    app (free_vars e')
      (flat_map (\pat ->
        case pat of {
         (,) ej ej' -> diff (free_vars ej') (free_vars ej)}) l);
   Try e0 e1 -> app (free_vars e0) (free_vars e1);
   Apply _ e' -> free_vars e'}

split_sum_list :: Type -> Type -> (([]) Expr) -> Prelude.Maybe
                  ((,) (([]) Expr) (([]) Expr))
split_sum_list t0 t1 l =
  case l of {
   ([]) -> Prelude.Just ((,) ([]) ([]));
   (:) e l' ->
    case e of {
     Apply f e1 ->
      case f of {
       Left t0' t1' ->
        case eqb4 eqb_type t0 t0' of {
         Prelude.True ->
          case eqb4 eqb_type t1 t1' of {
           Prelude.True ->
            case split_sum_list t0 t1 l' of {
             Prelude.Just p ->
              case p of {
               (,) l0 l1 -> Prelude.Just ((,) ((:) e1 l0) l1)};
             Prelude.Nothing -> Prelude.Nothing};
           Prelude.False -> Prelude.Nothing};
         Prelude.False -> Prelude.Nothing};
       Right t0' t1' ->
        case eqb4 eqb_type t0 t0' of {
         Prelude.True ->
          case eqb4 eqb_type t1 t1' of {
           Prelude.True ->
            case split_sum_list t0 t1 l' of {
             Prelude.Just p ->
              case p of {
               (,) l0 l1 -> Prelude.Just ((,) l0 ((:) e1 l1))};
             Prelude.Nothing -> Prelude.Nothing};
           Prelude.False -> Prelude.Nothing};
         Prelude.False -> Prelude.Nothing};
       _ -> Prelude.Nothing};
     _ -> Prelude.Nothing}}

add_to_qpair_list :: Expr -> Expr -> (([]) ((,) Expr (([]) Expr))) -> ([])
                     ((,) Expr (([]) Expr))
add_to_qpair_list e0 e1 l =
  case l of {
   ([]) -> (:) ((,) e0 ((:) e1 ([]))) ([]);
   (:) p l' ->
    case p of {
     (,) e0' l1 ->
      case eqb4 eqb_expr0 e0 e0' of {
       Prelude.True -> (:) ((,) e0 ((:) e1 l1)) l';
       Prelude.False -> (:) ((,) e0' l1) (add_to_qpair_list e0 e1 l')}}}

spread_qpair_list :: (([]) Expr) -> Prelude.Maybe
                     (([]) ((,) Expr (([]) Expr)))
spread_qpair_list l =
  case l of {
   ([]) -> Prelude.Just ([]);
   (:) e l' ->
    case e of {
     Qpair e0 e1 ->
      case spread_qpair_list l' of {
       Prelude.Just l0 -> Prelude.Just (add_to_qpair_list e0 e1 l0);
       Prelude.Nothing -> Prelude.Nothing};
     _ -> Prelude.Nothing}}

missing_span :: Type -> (([]) Expr) -> (([]) String) -> Prelude.Maybe
                (([]) Expr)
missing_span t l x0 =
  case t of {
   Void ->
    case l of {
     ([]) -> Prelude.Just ((:) (Var (fresh x0)) ([]));
     (:) y l0 ->
      case y of {
       Var x1 ->
        case l0 of {
         ([]) ->
          case mem x1 x0 of {
           Prelude.True -> Prelude.Nothing;
           Prelude.False -> Prelude.Just ([])};
         (:) _ _ -> Prelude.Nothing};
       _ -> Prelude.Nothing}};
   Qunit ->
    case l of {
     ([]) -> Prelude.Just ((:) (Var (fresh x0)) ([]));
     (:) e l0 ->
      case e of {
       Null ->
        case l0 of {
         ([]) -> Prelude.Just ([]);
         (:) _ _ -> Prelude.Nothing};
       Var x1 ->
        case l0 of {
         ([]) ->
          case mem x1 x0 of {
           Prelude.True -> Prelude.Nothing;
           Prelude.False -> Prelude.Just ([])};
         (:) _ _ -> Prelude.Nothing};
       _ -> Prelude.Nothing}};
   Superpos t0 t1 ->
    case l of {
     ([]) -> Prelude.Just ((:) (Var (fresh x0)) ([]));
     (:) e l0 ->
      case e of {
       Var x1 ->
        case l0 of {
         ([]) ->
          case mem x1 x0 of {
           Prelude.True -> Prelude.Nothing;
           Prelude.False -> Prelude.Just ([])};
         (:) _ _ ->
          case split_sum_list t0 t1 l of {
           Prelude.Just p ->
            case p of {
             (,) l1 l2 ->
              case missing_span t0 l1 x0 of {
               Prelude.Just l0' ->
                case missing_span t1 l2 x0 of {
                 Prelude.Just l1' -> Prelude.Just
                  (app (map (\x2 -> Apply (Left t0 t1) x2) l0')
                    (map (\x2 -> Apply (Right t0 t1) x2) l1'));
                 Prelude.Nothing -> Prelude.Nothing};
               Prelude.Nothing -> Prelude.Nothing}};
           Prelude.Nothing -> Prelude.Nothing}};
       _ ->
        case split_sum_list t0 t1 l of {
         Prelude.Just p ->
          case p of {
           (,) l1 l2 ->
            case missing_span t0 l1 x0 of {
             Prelude.Just l0' ->
              case missing_span t1 l2 x0 of {
               Prelude.Just l1' -> Prelude.Just
                (app (map (\x1 -> Apply (Left t0 t1) x1) l0')
                  (map (\x1 -> Apply (Right t0 t1) x1) l1'));
               Prelude.Nothing -> Prelude.Nothing};
             Prelude.Nothing -> Prelude.Nothing}};
         Prelude.Nothing -> Prelude.Nothing}}};
   Joint t0 t1 ->
    case l of {
     ([]) -> Prelude.Just ((:) (Var (fresh x0)) ([]));
     (:) e l0 ->
      case e of {
       Var x1 ->
        case l0 of {
         ([]) ->
          case mem x1 x0 of {
           Prelude.True -> Prelude.Nothing;
           Prelude.False -> Prelude.Just ([])};
         (:) _ _ ->
          case spread_qpair_list l of {
           Prelude.Just l' ->
            case missing_span t0 (map fst l')
                   (app x0 (flat_map free_vars (flat_map snd l'))) of {
             Prelude.Just l1 ->
              flat_map_maybe (\pat ->
                case pat of {
                 (,) e0 l2 ->
                  case missing_span t1 l2 (app x0 (free_vars e0)) of {
                   Prelude.Just l1' -> Prelude.Just
                    (map (\x2 -> Qpair e0 x2) l1');
                   Prelude.Nothing -> Prelude.Nothing}})
                (app (map (\e0 -> (,) e0 ([])) l1) l');
             Prelude.Nothing -> Prelude.Nothing};
           Prelude.Nothing -> Prelude.Nothing}};
       _ ->
        case spread_qpair_list l of {
         Prelude.Just l' ->
          case missing_span t0 (map fst l')
                 (app x0 (flat_map free_vars (flat_map snd l'))) of {
           Prelude.Just l1 ->
            flat_map_maybe (\pat ->
              case pat of {
               (,) e0 l2 ->
                case missing_span t1 l2 (app x0 (free_vars e0)) of {
                 Prelude.Just l1' -> Prelude.Just
                  (map (\x1 -> Qpair e0 x1) l1');
                 Prelude.Nothing -> Prelude.Nothing}})
              (app (map (\e0 -> (,) e0 ([])) l1) l');
           Prelude.Nothing -> Prelude.Nothing};
         Prelude.Nothing -> Prelude.Nothing}}}}

span_list :: Type -> (([]) Expr) -> (([]) String) -> Prelude.Maybe
             (([]) Expr)
span_list t l x0 =
  case missing_span t l x0 of {
   Prelude.Just l' -> Prelude.Just (app l' l);
   Prelude.Nothing -> Prelude.Nothing}

ortho_check :: Type -> (([]) Expr) -> Prelude.Bool
ortho_check t l =
  case span_list t l ([]) of {
   Prelude.Just _ -> Prelude.True;
   Prelude.Nothing -> Prelude.False}

dephase :: Type -> Expr -> ([]) Expr
dephase t e =
  case e of {
   Ctrl _ _ l t' ->
    case eqb4 eqb_type t t' of {
     Prelude.True ->
      flat_map (\pat -> case pat of {
                         (,) _ ej' -> dephase t ej'}) l;
     Prelude.False -> (:) e ([])};
   Apply f e' ->
    case f of {
     Rphase t' e0 gamma gamma' ->
      case e0 of {
       Var x0 ->
        case (Prelude.&&)
               ((Prelude.&&) (eqb4 eqb_type t t') (eqb4 eqb_string x x0))
               (eqb_real gamma gamma') of {
         Prelude.True -> dephase t e';
         Prelude.False -> (:) e ([])};
       _ -> (:) e ([])};
     _ -> (:) e ([])};
   _ -> (:) e ([])}

split_qpair_list :: (([]) Expr) -> Prelude.Maybe
                    ((,) (([]) Expr) (([]) Expr))
split_qpair_list l =
  case l of {
   ([]) -> Prelude.Just ((,) ([]) ([]));
   (:) e l' ->
    case e of {
     Qpair e0 e1 ->
      case split_qpair_list l' of {
       Prelude.Just p ->
        case p of {
         (,) l0 l1 -> Prelude.Just ((,) ((:) e0 l0) ((:) e1 l1))};
       Prelude.Nothing -> Prelude.Nothing};
     _ -> Prelude.Nothing}}

erases_check :: String -> Type -> (([]) Expr) -> Prelude.Bool
erases_check x0 t l =
  let {l' = flat_map (dephase t) l} in
  case forallb (eqb4 eqb_expr0 (Var x0)) l' of {
   Prelude.True -> Prelude.True;
   Prelude.False ->
    case t of {
     Joint t0 t1 ->
      case split_qpair_list l' of {
       Prelude.Just p ->
        case p of {
         (,) l0 l1 ->
          (Prelude.||) (erases_check x0 t0 l0) (erases_check x0 t1 l1)};
       Prelude.Nothing -> Prelude.False};
     _ -> Prelude.False}}

partition_context :: Set -> Context -> (,) Context Context
partition_context x0 g =
  case g of {
   ([]) -> (,) ([]) ([]);
   (:) p g' ->
    case p of {
     (,) x1 t ->
      case partition_context x0 g' of {
       (,) g0 g1 ->
        case mem x1 x0 of {
         Prelude.True -> (,) ((:) ((,) x1 t) g0) g1;
         Prelude.False -> (,) g0 ((:) ((,) x1 t) g1)}}}}

partition_pair_context :: Set -> Set -> Context -> Prelude.Maybe
                          ((,) ((,) Context Context) Context)
partition_pair_context x0 x1 d =
  case d of {
   ([]) -> Prelude.Just ((,) ((,) ([]) ([])) ([]));
   (:) p dp ->
    case p of {
     (,) x2 t ->
      case mem x2 x0 of {
       Prelude.True ->
        case mem x2 x1 of {
         Prelude.True ->
          case partition_pair_context x0 x1 dp of {
           Prelude.Just p0 ->
            case p0 of {
             (,) p1 d1 ->
              case p1 of {
               (,) d' d0 -> Prelude.Just ((,) ((,) ((:) ((,) x2 t) d') d0)
                d1)}};
           Prelude.Nothing -> Prelude.Nothing};
         Prelude.False ->
          case partition_pair_context x0 x1 dp of {
           Prelude.Just p0 ->
            case p0 of {
             (,) p1 d1 ->
              case p1 of {
               (,) d' d0 -> Prelude.Just ((,) ((,) d' ((:) ((,) x2 t) d0))
                d1)}};
           Prelude.Nothing -> Prelude.Nothing}};
       Prelude.False ->
        case mem x2 x1 of {
         Prelude.True ->
          case partition_pair_context x0 x1 dp of {
           Prelude.Just p0 ->
            case p0 of {
             (,) p1 d1 -> Prelude.Just ((,) p1 ((:) ((,) x2 t) d1))};
           Prelude.Nothing -> Prelude.Nothing};
         Prelude.False -> Prelude.Nothing}}}}

pattern_type_check :: (Context -> Context -> Expr -> Prelude.Maybe Type) ->
                      (Context -> Type -> Expr -> Prelude.Maybe Context) ->
                      Context -> Context -> Type -> Type -> ((,) Expr 
                      Expr) -> Prelude.Bool
pattern_type_check pure_type_check0 context_check0 g d t t' pat =
  case pat of {
   (,) ej ej' ->
    case context_check0 ([]) t ej of {
     Prelude.Just gj ->
      eqb4 (eqb_option eqb_type) (pure_type_check0 (app g gj) d ej')
        (Prelude.Just t');
     Prelude.Nothing -> Prelude.False}}

mixed_type_check :: (Context -> Context -> Expr -> Prelude.Maybe Type) ->
                    (Prog -> Prelude.Maybe Prog_type) -> Context -> Expr ->
                    Prelude.Maybe Type
mixed_type_check pure_type_check0 prog_type_check0 d e =
  case e of {
   Null -> pure_type_check0 ([]) d e;
   Var _ -> pure_type_check0 ([]) d e;
   Qpair e0 e1 ->
    case well_formed_check d of {
     Prelude.True ->
      case partition_pair_context (free_vars e0) (free_vars e1) d of {
       Prelude.Just p ->
        case p of {
         (,) p0 d1 ->
          case p0 of {
           (,) d' d0 ->
            case mixed_type_check pure_type_check0 prog_type_check0
                   (app d' d0) e0 of {
             Prelude.Just t0 ->
              case mixed_type_check pure_type_check0 prog_type_check0
                     (app d' d1) e1 of {
               Prelude.Just t1 -> Prelude.Just (Joint t0 t1);
               Prelude.Nothing -> Prelude.Nothing};
             Prelude.Nothing -> Prelude.Nothing}}};
       Prelude.Nothing -> Prelude.Nothing};
     Prelude.False -> Prelude.Nothing};
   Ctrl _ _ _ _ -> pure_type_check0 ([]) d e;
   Try e0 e1 ->
    case partition_context (free_vars e0) d of {
     (,) d0 d1 ->
      case disjointb (dom d0) (dom d1) of {
       Prelude.True ->
        case mixed_type_check pure_type_check0 prog_type_check0 d0 e0 of {
         Prelude.Just t0 ->
          case mixed_type_check pure_type_check0 prog_type_check0 d1 e1 of {
           Prelude.Just t1 ->
            case eqb4 eqb_type t0 t1 of {
             Prelude.True -> Prelude.Just t0;
             Prelude.False -> Prelude.Nothing};
           Prelude.Nothing -> Prelude.Nothing};
         Prelude.Nothing -> Prelude.Nothing};
       Prelude.False -> Prelude.Nothing}};
   Apply f e' ->
    case mixed_type_check pure_type_check0 prog_type_check0 d e' of {
     Prelude.Just t ->
      case prog_type_check0 f of {
       Prelude.Just p ->
        case p of {
         Coherent t0 t1 ->
          case eqb4 eqb_type t t0 of {
           Prelude.True -> Prelude.Just t1;
           Prelude.False -> Prelude.Nothing};
         Channel t0 t1 ->
          case eqb4 eqb_type t t0 of {
           Prelude.True -> Prelude.Just t1;
           Prelude.False -> Prelude.Nothing}};
       Prelude.Nothing -> Prelude.Nothing};
     Prelude.Nothing -> Prelude.Nothing}}

first_pattern_context_check :: (Context -> Type -> Expr -> Prelude.Maybe
                               Context) -> Context -> Type -> Type -> Expr ->
                               Expr -> Prelude.Maybe Context
first_pattern_context_check context_check0 g t t' ej ej' =
  case context_check0 ([]) t ej of {
   Prelude.Just gj -> context_check0 (app g gj) t' ej';
   Prelude.Nothing -> Prelude.Nothing}

mixed_context_check :: (Context -> Type -> Expr -> Prelude.Maybe Context) ->
                       (Prog -> Prelude.Maybe Prog_type) -> Type -> Expr ->
                       Prelude.Maybe Context
mixed_context_check context_check0 prog_type_check0 t e =
  case e of {
   Null -> context_check0 ([]) t e;
   Var _ -> context_check0 ([]) t e;
   Qpair e0 e1 ->
    case t of {
     Joint t0 t1 ->
      case mixed_context_check context_check0 prog_type_check0 t0 e0 of {
       Prelude.Just d0 ->
        case mixed_context_check context_check0 prog_type_check0 t1 e1 of {
         Prelude.Just d1 -> merge d0 d1;
         Prelude.Nothing -> Prelude.Nothing};
       Prelude.Nothing -> Prelude.Nothing};
     _ -> Prelude.Nothing};
   Ctrl _ _ _ _ -> context_check0 ([]) t e;
   Try e0 e1 ->
    case mixed_context_check context_check0 prog_type_check0 t e0 of {
     Prelude.Just d0 ->
      case mixed_context_check context_check0 prog_type_check0 t e1 of {
       Prelude.Just d1 ->
        case disjointb (dom d0) (dom d1) of {
         Prelude.True -> Prelude.Just (app d0 d1);
         Prelude.False -> Prelude.Nothing};
       Prelude.Nothing -> Prelude.Nothing};
     Prelude.Nothing -> Prelude.Nothing};
   Apply f e' ->
    case prog_type_check0 f of {
     Prelude.Just p ->
      case p of {
       Coherent t0 t1 ->
        case eqb4 eqb_type t t1 of {
         Prelude.True ->
          mixed_context_check context_check0 prog_type_check0 t0 e';
         Prelude.False -> Prelude.Nothing};
       Channel t0 t1 ->
        case eqb4 eqb_type t t1 of {
         Prelude.True ->
          mixed_context_check context_check0 prog_type_check0 t0 e';
         Prelude.False -> Prelude.Nothing}};
     Prelude.Nothing -> Prelude.Nothing}}

pure_type_check :: Context -> Context -> Expr -> Prelude.Maybe Type
pure_type_check g d e =
  let {mixed_type_check0 = mixed_type_check pure_type_check prog_type_check}
  in
  case e of {
   Null ->
    case well_formed_check g of {
     Prelude.True ->
      case d of {
       ([]) -> Prelude.Just Qunit;
       (:) _ _ -> Prelude.Nothing};
     Prelude.False -> Prelude.Nothing};
   Var x0 ->
    case well_formed_check g of {
     Prelude.True ->
      case d of {
       ([]) -> context_find g x0;
       (:) p l ->
        case p of {
         (,) x' t ->
          case l of {
           ([]) ->
            case eqb4 eqb_string x0 x' of {
             Prelude.True ->
              case context_find g x0 of {
               Prelude.Just _ -> Prelude.Nothing;
               Prelude.Nothing -> Prelude.Just t};
             Prelude.False -> Prelude.Nothing};
           (:) _ _ -> Prelude.Nothing}}};
     Prelude.False -> Prelude.Nothing};
   Qpair e0 e1 ->
    case well_formed_check (app g d) of {
     Prelude.True ->
      case partition_pair_context (free_vars e0) (free_vars e1) d of {
       Prelude.Just p ->
        case p of {
         (,) p0 d1 ->
          case p0 of {
           (,) d' d0 ->
            case pure_type_check g (app d' d0) e0 of {
             Prelude.Just t0 ->
              case pure_type_check g (app d' d1) e1 of {
               Prelude.Just t1 -> Prelude.Just (Joint t0 t1);
               Prelude.Nothing -> Prelude.Nothing};
             Prelude.Nothing -> Prelude.Nothing}}};
       Prelude.Nothing -> Prelude.Nothing};
     Prelude.False -> Prelude.Nothing};
   Ctrl e0 t l t' ->
    let {xe = free_vars e0} in
    case partition_context xe d of {
     (,) d0 d' ->
      case split l of {
       (,) ej ej' ->
        case partition_context xe g of {
         (,) g0 g' ->
          case (Prelude.&&)
                 ((Prelude.&&)
                   ((Prelude.&&)
                     ((Prelude.&&)
                       (well_formed_check (app g0 (app g' (app d0 d'))))
                       (eqb4 (eqb_option eqb_type)
                         (mixed_type_check0 (app g0 d0) e0) (Prelude.Just t)))
                     (ortho_check t ej))
                   (forallb
                     (pattern_type_check pure_type_check context_check
                       (app g0 g') (app d0 d') t t') l))
                 (forallb (\x0 -> erases_check x0 t' ej') (dom d0)) of {
           Prelude.True -> Prelude.Just t';
           Prelude.False -> Prelude.Nothing}}}};
   Try _ _ -> Prelude.Nothing;
   Apply f e' ->
    case pure_type_check g d e' of {
     Prelude.Just t' ->
      case prog_type_check f of {
       Prelude.Just p ->
        case p of {
         Coherent t0 t1 ->
          case eqb4 eqb_type t' t0 of {
           Prelude.True -> Prelude.Just t1;
           Prelude.False -> Prelude.Nothing};
         Channel _ _ -> Prelude.Nothing};
       Prelude.Nothing -> Prelude.Nothing};
     Prelude.Nothing -> Prelude.Nothing}}

context_check :: Context -> Type -> Expr -> Prelude.Maybe Context
context_check g t e =
  let {
   mixed_context_check0 = mixed_context_check context_check prog_type_check}
  in
  case e of {
   Null ->
    case t of {
     Qunit ->
      case well_formed_check g of {
       Prelude.True -> Prelude.Just ([]);
       Prelude.False -> Prelude.Nothing};
     _ -> Prelude.Nothing};
   Var x0 ->
    case well_formed_check g of {
     Prelude.True ->
      case context_find g x0 of {
       Prelude.Just t' ->
        case eqb4 eqb_type t t' of {
         Prelude.True -> Prelude.Just ([]);
         Prelude.False -> Prelude.Nothing};
       Prelude.Nothing -> Prelude.Just ((:) ((,) x0 t) ([]))};
     Prelude.False -> Prelude.Nothing};
   Qpair e0 e1 ->
    case t of {
     Joint t0 t1 ->
      case context_check g t0 e0 of {
       Prelude.Just d0 ->
        case context_check g t1 e1 of {
         Prelude.Just d1 -> merge d0 d1;
         Prelude.Nothing -> Prelude.Nothing};
       Prelude.Nothing -> Prelude.Nothing};
     _ -> Prelude.Nothing};
   Ctrl e' t0 l t1 ->
    case split l of {
     (,) ej ej' ->
      case eqb4 eqb_type t t1 of {
       Prelude.True ->
        case mixed_context_check0 t0 e' of {
         Prelude.Just d ->
          case l of {
           ([]) -> remove_all g d;
           (:) p l0 ->
            case p of {
             (,) e0 e0' ->
              case first_pattern_context_check context_check g t0 t1 e0 e0' of {
               Prelude.Just d0 ->
                case (Prelude.&&)
                       ((Prelude.&&)
                         ((Prelude.&&) (inclusionb d (app g d0))
                           (ortho_check t0 ej))
                         (forallb
                           (pattern_type_check pure_type_check context_check
                             g d0 t0 t1) l0))
                       (forallb (\x0 -> erases_check x0 t1 ej') (dom d)) of {
                 Prelude.True -> Prelude.Just d0;
                 Prelude.False -> Prelude.Nothing};
               Prelude.Nothing -> Prelude.Nothing}}};
         Prelude.Nothing -> Prelude.Nothing};
       Prelude.False -> Prelude.Nothing}};
   Try _ _ -> Prelude.Nothing;
   Apply f e' ->
    case prog_type_check f of {
     Prelude.Just p ->
      case p of {
       Coherent t0 t1 ->
        case eqb4 eqb_type t t1 of {
         Prelude.True -> context_check g t0 e';
         Prelude.False -> Prelude.Nothing};
       Channel _ _ -> Prelude.Nothing};
     Prelude.Nothing -> Prelude.Nothing}}

prog_type_check :: Prog -> Prelude.Maybe Prog_type
prog_type_check f =
  let {mixed_type_check0 = mixed_type_check pure_type_check prog_type_check}
  in
  case f of {
   U3 _ _ _ -> Prelude.Just (Coherent bit bit);
   Left t0 t1 -> Prelude.Just (Coherent t0 (Superpos t0 t1));
   Right t0 t1 -> Prelude.Just (Coherent t1 (Superpos t0 t1));
   Lambda e t e' ->
    case context_check ([]) t e of {
     Prelude.Just d ->
      case pure_type_check ([]) d e' of {
       Prelude.Just t' -> Prelude.Just (Coherent t t');
       Prelude.Nothing ->
        case mixed_type_check0 (restriction d (free_vars e')) e' of {
         Prelude.Just t' -> Prelude.Just (Channel t t');
         Prelude.Nothing -> Prelude.Nothing}};
     Prelude.Nothing -> Prelude.Nothing};
   Rphase t e _ _ ->
    case context_check ([]) t e of {
     Prelude.Just _ -> Prelude.Just (Coherent t t);
     Prelude.Nothing -> Prelude.Nothing}}

