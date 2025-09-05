; Z3 invocation started by F*
; F* version: 2025.08.07~dev -- commit hash: unset
; Z3 version (according to F*): 4.8.5

(set-option :global-decls false)
(set-option :smt.mbqi false)
(set-option :auto_config false)
(set-option :produce-unsat-cores true)
(set-option :model true)
(set-option :smt.case_split 3)
(set-option :smt.relevancy 2)
(set-option :smt.arith.solver 2)


(declare-sort FString)
(declare-fun FString_constr_id (FString) Int)

(declare-sort Term)
(declare-fun Term_constr_id (Term) Int)
(declare-sort Dummy_sort)
(declare-fun Dummy_value () Dummy_sort)
(declare-datatypes () ((Fuel 
(ZFuel) 
(SFuel (prec Fuel)))))
(declare-fun MaxIFuel () Fuel)
(declare-fun MaxFuel () Fuel)
(declare-fun PreType (Term) Term)
(declare-fun Valid (Term) Bool)
(declare-fun HasTypeFuel (Fuel Term Term) Bool)
(define-fun HasTypeZ ((x Term) (t Term)) Bool
(HasTypeFuel ZFuel x t))
(define-fun HasType ((x Term) (t Term)) Bool
(HasTypeFuel MaxIFuel x t))
(declare-fun IsTotFun (Term) Bool)

                ;;fuel irrelevance
(assert (forall ((f Fuel) (x Term) (t Term))
(! (= (HasTypeFuel (SFuel f) x t)
(HasTypeZ x t))
:pattern ((HasTypeFuel (SFuel f) x t)))))
(declare-fun NoHoist (Term Bool) Bool)
;;no-hoist
(assert (forall ((dummy Term) (b Bool))
(! (= (NoHoist dummy b) b)
:pattern ((NoHoist dummy b)))))
(define-fun  IsTyped ((x Term)) Bool
(exists ((t Term)) (HasTypeZ x t)))
(declare-fun ApplyTF (Term Fuel) Term)
(declare-fun ApplyTT (Term Term) Term)
(declare-fun Prec (Term Term) Bool)
(assert (forall ((x Term) (y Term) (z Term))
(! (implies (and (Prec x y) (Prec y z)) (Prec x z))
:pattern ((Prec x z) (Prec x y)))))
(assert (forall ((x Term) (y Term))
(implies (Prec x y)
(not (Prec y x)))))
(declare-fun Closure (Term) Term)
(declare-fun ConsTerm (Term Term) Term)
(declare-fun ConsFuel (Fuel Term) Term)
(declare-fun Tm_uvar (Int) Term)
(define-fun Reify ((x Term)) Term x)
(declare-fun Prims.precedes (Term Term Term Term) Term)
(declare-fun Range_const (Int) Term)
(declare-fun _mul (Int Int) Int)
(declare-fun _div (Int Int) Int)
(declare-fun _mod (Int Int) Int)
(declare-fun __uu__PartialApp () Term)
(assert (forall ((x Int) (y Int)) (! (= (_mul x y) (* x y)) :pattern ((_mul x y)))))
(assert (forall ((x Int) (y Int)) (! (= (_div x y) (div x y)) :pattern ((_div x y)))))
(assert (forall ((x Int) (y Int)) (! (= (_mod x y) (mod x y)) :pattern ((_mod x y)))))
(declare-fun _rmul (Real Real) Real)
(declare-fun _rdiv (Real Real) Real)
(assert (forall ((x Real) (y Real)) (! (= (_rmul x y) (* x y)) :pattern ((_rmul x y)))))
(assert (forall ((x Real) (y Real)) (! (= (_rdiv x y) (/ x y)) :pattern ((_rdiv x y)))))
(define-fun Unreachable () Bool false); <start constructor FString_const>
; Constructor
(declare-fun FString_const (Int) FString)
; Constructor distinct
;;; Fact-ids: 
(assert
 (! (forall ((@u0 Int))
   (! (= 0 (FString_constr_id (FString_const @u0)))
    :pattern ((FString_const @u0))
    :qid constructor_distinct_FString_const))
  :named constructor_distinct_FString_const))
; Projector
(declare-fun FString_const_proj_0 (FString) Int)
; Projection inverse
;;; Fact-ids: 
(assert
 (! (forall ((@u0 Int))
   (! (= (FString_const_proj_0 (FString_const @u0)) @u0)
    :pattern ((FString_const @u0))
    :qid projection_inverse_FString_const_proj_0))
  :named projection_inverse_FString_const_proj_0))
; Discriminator definition
(define-fun is-FString_const ((__@u0 FString)) Bool
 (and (= (FString_constr_id __@u0) 0) (= __@u0 (FString_const (FString_const_proj_0 __@u0)))))
; </end constructor FString_const>
; <start constructor Tm_type>
; Constructor
(declare-fun Tm_type () Term)
; Constructor distinct
;;; Fact-ids: 
(assert (! (= 2 (Term_constr_id Tm_type)) :named constructor_distinct_Tm_type))
; Discriminator definition
(define-fun is-Tm_type ((__@x0 Term)) Bool (and (= (Term_constr_id __@x0) 2) (= __@x0 Tm_type)))
; </end constructor Tm_type>
; <start constructor Tm_arrow>
; Constructor
(declare-fun Tm_arrow (Int) Term)
; Constructor distinct
;;; Fact-ids: 
(assert
 (! (forall ((@u0 Int))
   (! (= 3 (Term_constr_id (Tm_arrow @u0)))
    :pattern ((Tm_arrow @u0))
    :qid constructor_distinct_Tm_arrow))
  :named constructor_distinct_Tm_arrow))
; Projector
(declare-fun Tm_arrow_id (Term) Int)
; Projection inverse
;;; Fact-ids: 
(assert
 (! (forall ((@u0 Int))
   (! (= (Tm_arrow_id (Tm_arrow @u0)) @u0)
    :pattern ((Tm_arrow @u0))
    :qid projection_inverse_Tm_arrow_id))
  :named projection_inverse_Tm_arrow_id))
; Discriminator definition
(define-fun is-Tm_arrow ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0) 3) (= __@x0 (Tm_arrow (Tm_arrow_id __@x0)))))
; </end constructor Tm_arrow>
; <start constructor Tm_unit>
; Constructor
(declare-fun Tm_unit () Term)
; Constructor distinct
;;; Fact-ids: 
(assert (! (= 6 (Term_constr_id Tm_unit)) :named constructor_distinct_Tm_unit))
; Discriminator definition
(define-fun is-Tm_unit ((__@x0 Term)) Bool (and (= (Term_constr_id __@x0) 6) (= __@x0 Tm_unit)))
; </end constructor Tm_unit>
; <start constructor BoxInt>
; Constructor
(declare-fun BoxInt (Int) Term)
; Constructor distinct
;;; Fact-ids: 
(assert
 (! (forall ((@u0 Int))
   (! (= 7 (Term_constr_id (BoxInt @u0))) :pattern ((BoxInt @u0)) :qid constructor_distinct_BoxInt))
  :named constructor_distinct_BoxInt))
; Projector
(declare-fun BoxInt_proj_0 (Term) Int)
; Projection inverse
;;; Fact-ids: 
(assert
 (! (forall ((@u0 Int))
   (! (= (BoxInt_proj_0 (BoxInt @u0)) @u0)
    :pattern ((BoxInt @u0))
    :qid projection_inverse_BoxInt_proj_0))
  :named projection_inverse_BoxInt_proj_0))
; Discriminator definition
(define-fun is-BoxInt ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0) 7) (= __@x0 (BoxInt (BoxInt_proj_0 __@x0)))))
; </end constructor BoxInt>
; <start constructor BoxBool>
; Constructor
(declare-fun BoxBool (Bool) Term)
; Constructor distinct
;;; Fact-ids: 
(assert
 (! (forall ((@u0 Bool))
   (! (= 8 (Term_constr_id (BoxBool @u0)))
    :pattern ((BoxBool @u0))
    :qid constructor_distinct_BoxBool))
  :named constructor_distinct_BoxBool))
; Projector
(declare-fun BoxBool_proj_0 (Term) Bool)
; Projection inverse
;;; Fact-ids: 
(assert
 (! (forall ((@u0 Bool))
   (! (= (BoxBool_proj_0 (BoxBool @u0)) @u0)
    :pattern ((BoxBool @u0))
    :qid projection_inverse_BoxBool_proj_0))
  :named projection_inverse_BoxBool_proj_0))
; Discriminator definition
(define-fun is-BoxBool ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0) 8) (= __@x0 (BoxBool (BoxBool_proj_0 __@x0)))))
; </end constructor BoxBool>
; <start constructor BoxString>
; Constructor
(declare-fun BoxString (FString) Term)
; Constructor distinct
;;; Fact-ids: 
(assert
 (! (forall ((@u0 FString))
   (! (= 9 (Term_constr_id (BoxString @u0)))
    :pattern ((BoxString @u0))
    :qid constructor_distinct_BoxString))
  :named constructor_distinct_BoxString))
; Projector
(declare-fun BoxString_proj_0 (Term) FString)
; Projection inverse
;;; Fact-ids: 
(assert
 (! (forall ((@u0 FString))
   (! (= (BoxString_proj_0 (BoxString @u0)) @u0)
    :pattern ((BoxString @u0))
    :qid projection_inverse_BoxString_proj_0))
  :named projection_inverse_BoxString_proj_0))
; Discriminator definition
(define-fun is-BoxString ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0) 9) (= __@x0 (BoxString (BoxString_proj_0 __@x0)))))
; </end constructor BoxString>
; <start constructor BoxReal>
; Constructor
(declare-fun BoxReal (Real) Term)
; Constructor distinct
;;; Fact-ids: 
(assert
 (! (forall ((@u0 Real))
   (! (= 10 (Term_constr_id (BoxReal @u0)))
    :pattern ((BoxReal @u0))
    :qid constructor_distinct_BoxReal))
  :named constructor_distinct_BoxReal))
; Projector
(declare-fun BoxReal_proj_0 (Term) Real)
; Projection inverse
;;; Fact-ids: 
(assert
 (! (forall ((@u0 Real))
   (! (= (BoxReal_proj_0 (BoxReal @u0)) @u0)
    :pattern ((BoxReal @u0))
    :qid projection_inverse_BoxReal_proj_0))
  :named projection_inverse_BoxReal_proj_0))
; Discriminator definition
(define-fun is-BoxReal ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0) 10) (= __@x0 (BoxReal (BoxReal_proj_0 __@x0)))))
; </end constructor BoxReal>
(declare-fun Prims.precedes@tok () Term)
(assert
(forall ((@x0 Term) (@x1 Term) (@x2 Term) (@x3 Term))
(! (= (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.precedes@tok @x0) @x1) @x2) @x3)
        (Prims.precedes @x0 @x1 @x2 @x3))
:pattern ((ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.precedes@tok @x0) @x1) @x2) @x3)))))

(declare-fun Prims.lex_t () Term)
(assert (forall ((t1 Term) (t2 Term) (e1 Term) (e2 Term))
(! (iff (Valid (Prims.precedes t1 t2 e1 e2))
(Valid (Prims.precedes Prims.lex_t Prims.lex_t e1 e2)))
:pattern (Prims.precedes t1 t2 e1 e2))))
(assert (forall ((t1 Term) (t2 Term))
(! (iff (Valid (Prims.precedes Prims.lex_t Prims.lex_t t1 t2)) 
(Prec t1 t2))
:pattern ((Prims.precedes Prims.lex_t Prims.lex_t t1 t2)))))
(assert (forall ((e Term) (t Term))
(! (implies (HasType e t)
(Valid t))
:pattern ((HasType e t)
(Valid t))
:qid __prelude_valid_intro)))

; Externals for module Prims
; <Start encoding val Prims.attribute>
(declare-fun Prims.attribute () Term)
; </end encoding val Prims.attribute>

; <Start encoding val Prims.cps>
(declare-fun Prims.cps () Term)
; </end encoding val Prims.cps>

; <Start encoding val Prims.tac_opaque>
(declare-fun Prims.tac_opaque () Term)
; </end encoding val Prims.tac_opaque>

; <Start encoding val Prims.projector>
(declare-fun Prims.projector () Term)
; </end encoding val Prims.projector>

; <Start encoding val Prims.discriminator>
(declare-fun Prims.discriminator () Term)
; </end encoding val Prims.discriminator>

; <Start encoding val Prims.unrefine>
(declare-fun Prims.unrefine () Term)
; </end encoding val Prims.unrefine>

; <Start encoding val Prims.do_not_unrefine>
(declare-fun Prims.do_not_unrefine () Term)
; </end encoding val Prims.do_not_unrefine>

; <Start encoding val Prims.hasEq>
(declare-fun Prims.hasEq (Term) Term)
(declare-fun Tm_arrow_ef9cb512a25ee351fa5536d617490497 () Term)
(declare-fun Prims.hasEq@tok () Term)
; </end encoding val Prims.hasEq>

; <Start encoding let eqtype>
(declare-fun Prims.eqtype () Term)
(declare-fun Tm_refine_414d0a9f578ab0048252f8c8f552b99f () Term)
; </end encoding let eqtype>

; <Start encoding val Prims.bool>
(declare-fun Prims.bool () Term)
; </end encoding val Prims.bool>

; <Start encoding type Prims.empty>
; Constructor
(declare-fun Prims.empty () Term)
; <start constructor Prims.empty>
; Discriminator definition
(define-fun is-Prims.empty ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0) 111) (= __@x0 Prims.empty)))
; </end constructor Prims.empty>
; </end encoding type Prims.empty>

; <Start encoding type Prims.trivial>
; Constructor
(declare-fun Prims.trivial () Term)
; Constructor
(declare-fun Prims.T () Term)
; data constructor proxy: Prims.T
(declare-fun Prims.T@tok () Term)
; <start constructor Prims.trivial>
; Discriminator definition
(define-fun is-Prims.trivial ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0) 116) (= __@x0 Prims.trivial)))
; </end constructor Prims.trivial>
; <start constructor Prims.T>
; Discriminator definition
(define-fun is-Prims.T ((__@x0 Term)) Bool (and (= (Term_constr_id __@x0) 122) (= __@x0 Prims.T)))
; </end constructor Prims.T>
; </end encoding type Prims.trivial>

; <Start encoding val Prims.uu___is_T>
(declare-fun Prims.uu___is_T (Term) Term)
(declare-fun Tm_arrow_053f01f066524059a49c5dc621e6494a () Term)
(declare-fun Prims.uu___is_T@tok () Term)
; </end encoding val Prims.uu___is_T>

; <Start encoding val Prims.unit>
(declare-fun Prims.unit () Term)
; </end encoding val Prims.unit>

; <Start encoding let squash>
(declare-fun Prims.squash (Term) Term)

(declare-fun Prims.squash@tok () Term)
(declare-fun Tm_refine_2de20c066034c13bf76e9c0b94f4806c (Term) Term)
; </end encoding let squash>

; <Start encoding let auto_squash>
(declare-fun Prims.auto_squash (Term) Term)

(declare-fun Prims.auto_squash@tok () Term)
; </end encoding let auto_squash>

; <Start encoding let logical>
(declare-fun Prims.logical () Term)
; </end encoding let logical>

; <Start encoding val Prims.smt_theory_symbol>
(declare-fun Prims.smt_theory_symbol () Term)
; </end encoding val Prims.smt_theory_symbol>

; <Start encoding let l_True>
(declare-fun Prims.l_True () Term)
; </end encoding let l_True>

; <Start encoding let l_False>
(declare-fun Prims.l_False () Term)
; </end encoding let l_False>

; <Start encoding type Prims.equals>
; Constructor
(declare-fun Prims.equals (Term Term Term) Term)
; token
(declare-fun Prims.equals@tok () Term)
; Constructor
(declare-fun Prims.Refl (Term Term) Term)
; Constructor base
(declare-fun Prims.Refl@base () Term)
; data constructor proxy: Prims.Refl
(declare-fun Prims.Refl@tok () Term)
(declare-fun Tm_arrow_8e00c6263684633abbc1d1a87608e391 () Term)
; <start constructor Prims.equals>
; Discriminator definition
(define-fun is-Prims.equals ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 134)
  (exists ((@x0 Term) (@x1 Term) (@x2 Term))
   (! (= __@x0 (Prims.equals @x0 @x1 @x2)) :qid is-Prims.equals))))
; </end constructor Prims.equals>
; <start constructor Prims.Refl>
; Discriminator definition
(define-fun is-Prims.Refl ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 141)
  (exists ((@x0 Term) (@x1 Term)) (! (= __@x0 (Prims.Refl @x0 @x1)) :qid is-Prims.Refl))))
; </end constructor Prims.Refl>
; </end encoding type Prims.equals>

; <Start encoding val Prims.uu___is_Refl>
(declare-fun Prims.uu___is_Refl (Term Term Term Term) Term)
(declare-fun Tm_arrow_2a4540f76c8969717ea911077d7b4d15 () Term)
(declare-fun Prims.uu___is_Refl@tok () Term)
; </end encoding val Prims.uu___is_Refl>

; <Start encoding let eq2>
(declare-fun Prims.eq2 (Term Term Term) Term)
(declare-fun Tm_arrow_1ec40cec1da281b45a559c74dd57f3b7 () Term)
(declare-fun Prims.eq2@tok () Term)
; </end encoding let eq2>

; <Start encoding let b2t>
(declare-fun Prims.b2t (Term) Term)
; </end encoding let b2t>

; <Start encoding type Prims.pair>
; Constructor
(declare-fun Prims.pair (Term Term) Term)
; token
(declare-fun Prims.pair@tok () Term)
; Constructor
(declare-fun Prims.Pair (Term Term Term Term) Term)
; Projector
(declare-fun Prims.Pair_p (Term) Term)
; Projector
(declare-fun Prims.Pair_q (Term) Term)
; Projector
(declare-fun Prims.Pair__1 (Term) Term)
; Projector
(declare-fun Prims.Pair__2 (Term) Term)
; data constructor proxy: Prims.Pair
(declare-fun Prims.Pair@tok () Term)
(declare-fun Tm_arrow_e2b0096073073582c70f249d40f91c5d () Term)
; <start constructor Prims.pair>
; Discriminator definition
(define-fun is-Prims.pair ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 150)
  (exists ((@x0 Term) (@x1 Term)) (! (= __@x0 (Prims.pair @x0 @x1)) :qid is-Prims.pair))))
; </end constructor Prims.pair>
; <start constructor Prims.Pair>
; Discriminator definition
(define-fun is-Prims.Pair ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 157)
  (=
   __@x0
   (Prims.Pair (Prims.Pair_p __@x0) (Prims.Pair_q __@x0) (Prims.Pair__1 __@x0) (Prims.Pair__2 __@x0)))))
; </end constructor Prims.Pair>
; </end encoding type Prims.pair>

; <Start encoding val Prims.uu___is_Pair>
(declare-fun Prims.uu___is_Pair (Term Term Term) Term)
(declare-fun Tm_arrow_0a519c999e1325381ee4c9b1d93a06b2 () Term)
(declare-fun Prims.uu___is_Pair@tok () Term)
; </end encoding val Prims.uu___is_Pair>

; <Start encoding val Prims.__proj__Pair__item___1>
(declare-fun Prims.__proj__Pair__item___1 (Term Term Term) Term)
(declare-fun Tm_arrow_214b45775d1504fb2699ff0d156b6857 () Term)
(declare-fun Prims.__proj__Pair__item___1@tok () Term)
; </end encoding val Prims.__proj__Pair__item___1>

; <Start encoding val Prims.__proj__Pair__item___2>
(declare-fun Prims.__proj__Pair__item___2 (Term Term Term) Term)
(declare-fun Tm_arrow_1b97dbe8f5eb289f51cc2556690371e3 () Term)
(declare-fun Prims.__proj__Pair__item___2@tok () Term)
; </end encoding val Prims.__proj__Pair__item___2>

; <Start encoding let l_and>
(declare-fun Prims.l_and (Term Term) Term)
(declare-fun Tm_arrow_289ee2cc5874944bf725b9e3db8c0fd6 () Term)
(declare-fun Prims.l_and@tok () Term)
; </end encoding let l_and>

; <Start encoding type Prims.sum>
; Constructor
(declare-fun Prims.sum (Term Term) Term)
; token
(declare-fun Prims.sum@tok () Term)
; Constructor
(declare-fun Prims.Left (Term Term Term) Term)
; Projector
(declare-fun Prims.Left_p (Term) Term)
; Projector
(declare-fun Prims.Left_q (Term) Term)
; Projector
(declare-fun Prims.Left_v (Term) Term)
; data constructor proxy: Prims.Left
(declare-fun Prims.Left@tok () Term)
; Constructor
(declare-fun Prims.Right (Term Term Term) Term)
; Projector
(declare-fun Prims.Right_p (Term) Term)
; Projector
(declare-fun Prims.Right_q (Term) Term)
; Projector
(declare-fun Prims.Right_v (Term) Term)
; data constructor proxy: Prims.Right
(declare-fun Prims.Right@tok () Term)
(declare-fun Tm_arrow_4ef073c03ed003774fe6ccb4064aeebd () Term)
(declare-fun Tm_arrow_c537ccd7fef2183d55f1a6960ee793b0 () Term)
; <start constructor Prims.sum>
; Discriminator definition
(define-fun is-Prims.sum ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 169)
  (exists ((@x0 Term) (@x1 Term)) (! (= __@x0 (Prims.sum @x0 @x1)) :qid is-Prims.sum))))
; </end constructor Prims.sum>
; <start constructor Prims.Left>
; Discriminator definition
(define-fun is-Prims.Left ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 176)
  (= __@x0 (Prims.Left (Prims.Left_p __@x0) (Prims.Left_q __@x0) (Prims.Left_v __@x0)))))
; </end constructor Prims.Left>
; <start constructor Prims.Right>
; Discriminator definition
(define-fun is-Prims.Right ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 181)
  (= __@x0 (Prims.Right (Prims.Right_p __@x0) (Prims.Right_q __@x0) (Prims.Right_v __@x0)))))
; </end constructor Prims.Right>
; </end encoding type Prims.sum>

; <Start encoding val Prims.uu___is_Left>
(declare-fun Prims.uu___is_Left (Term Term Term) Term)
(declare-fun Tm_arrow_3c254c463840bdea2ca63f23cf7c2f0c () Term)
(declare-fun Prims.uu___is_Left@tok () Term)
; </end encoding val Prims.uu___is_Left>

; <Start encoding val Prims.__proj__Left__item__v>
(declare-fun Tm_refine_6140be01a70b18051829f178aaf0270b (Term Term) Term)
(declare-fun Prims.__proj__Left__item__v (Term Term Term) Term)

(declare-fun Tm_arrow_aaf070885513892396497eef726adce1 () Term)
(declare-fun Prims.__proj__Left__item__v@tok () Term)
; </end encoding val Prims.__proj__Left__item__v>

; <Start encoding val Prims.uu___is_Right>
(declare-fun Prims.uu___is_Right (Term Term Term) Term)

(declare-fun Prims.uu___is_Right@tok () Term)
; </end encoding val Prims.uu___is_Right>

; <Start encoding val Prims.__proj__Right__item__v>
(declare-fun Tm_refine_43ea5cf89e866ce271f97bd6ce102588 (Term Term) Term)
(declare-fun Prims.__proj__Right__item__v (Term Term Term) Term)

(declare-fun Tm_arrow_4ae0e7dd85e55aec7e8190dea6e3997f () Term)
(declare-fun Prims.__proj__Right__item__v@tok () Term)
; </end encoding val Prims.__proj__Right__item__v>

; <Start encoding let l_or>
(declare-fun Prims.l_or (Term Term) Term)

(declare-fun Prims.l_or@tok () Term)
; </end encoding let l_or>

; <Start encoding let l_imp>
(declare-fun Prims.l_imp (Term Term) Term)

(declare-fun Prims.l_imp@tok () Term)
(declare-fun Tm_ghost_arrow_0283b8a2a36bbec52abac4e3d837674a (Term Term) Term)
; </end encoding let l_imp>

; <Start encoding let l_iff>
(declare-fun Prims.l_iff (Term Term) Term)

(declare-fun Prims.l_iff@tok () Term)
; </end encoding let l_iff>

; <Start encoding let l_not>
(declare-fun Prims.l_not (Term) Term)
(declare-fun Tm_arrow_8178e3b6934aa50ea45bb0ccea2d9711 () Term)
(declare-fun Prims.l_not@tok () Term)
; </end encoding let l_not>

; <Skipped let l_ITE/>

; <Skipped val Prims.precedes/>

; <Start encoding val Prims.string>
(declare-fun Prims.string () Term)
; </end encoding val Prims.string>

; <Start encoding val Prims.warn_on_use>
(declare-fun Prims.warn_on_use (Term) Term)
(declare-fun Tm_arrow_2863eb88d7490a9c3cf347c16ca04740 () Term)
(declare-fun Prims.warn_on_use@tok () Term)
; </end encoding val Prims.warn_on_use>

; <Start encoding val Prims.deprecated>
(declare-fun Prims.deprecated (Term) Term)

(declare-fun Prims.deprecated@tok () Term)
; </end encoding val Prims.deprecated>

; <Start encoding val Prims.has_type>
(declare-fun Prims.has_type (Term Term Term) Term)
(declare-fun Tm_arrow_b5d8ed0243b8c7c893f2b329de57c62b () Term)
(declare-fun Prims.has_type@tok () Term)
; </end encoding val Prims.has_type>

; <Start encoding let l_Forall>
(declare-fun Tm_arrow_2eaa01e78f73e9bab5d0955fc1a662da (Term) Term)
(declare-fun Prims.l_Forall (Term Term) Term)

(declare-fun Tm_arrow_977ec6901669a051ac66211b8e72666a () Term)
(declare-fun Prims.l_Forall@tok () Term)

(declare-fun Tm_ghost_arrow_3aa447697277bb40c9738c9125c3e80f (Term Term) Term)
; </end encoding let l_Forall>

; <Skipped #push-options "--warn_error -288"/>

; <Start encoding let subtype_of>
(declare-fun Prims.subtype_of (Term Term) Term)
(declare-fun Tm_arrow_28becc0427b69ebf63ea956148504d97 () Term)
(declare-fun Prims.subtype_of@tok () Term)
; </end encoding let subtype_of>

; <Skipped #pop-options/>

; <Start encoding let prop>
(declare-fun Prims.prop () Term)
(declare-fun Tm_refine_73f210ca6e0061ed4a3150f69b8f33bf () Term)
; </end encoding let prop>

; <Start encoding let pure_pre>
(declare-fun Prims.pure_pre () Term)
; </end encoding let pure_pre>

; <Start encoding let pure_post'>
(declare-fun Prims.pure_post_ (Term Term) Term)
(declare-fun Tm_arrow_e4cf09589736facd1137944a1f5a00a6 () Term)
(declare-fun Prims.pure_post_@tok () Term)
(declare-fun Tm_refine_8d65e998a07dd53ec478e27017d9dba5 (Term Term) Term)
(declare-fun Tm_arrow_92458cff82f9ffee1f6e26a1c0c579f3 (Term Term) Term)
; </end encoding let pure_post'>

; <Start encoding let pure_post>
(declare-fun Prims.pure_post (Term) Term)

(declare-fun Prims.pure_post@tok () Term)
; </end encoding let pure_post>

; <Start encoding let pure_wp'>
(declare-fun Prims.pure_wp_ (Term) Term)

(declare-fun Prims.pure_wp_@tok () Term)
(declare-fun Tm_arrow_e5c03abbf8b0946a9aa7ee31bb7999a4 (Term) Term)
; </end encoding let pure_wp'>

; <Start encoding let pure_wp_monotonic0>
(declare-fun Prims.pure_wp_monotonic0 (Term Term) Term)
(declare-fun Tm_arrow_85436e2c1c64a4dd0159a737ef5b212e () Term)
(declare-fun Prims.pure_wp_monotonic0@tok () Term)
; </end encoding let pure_wp_monotonic0>

; <Start encoding let pure_wp_monotonic>
(declare-fun Prims.pure_wp_monotonic (Term Term) Term)

(declare-fun Prims.pure_wp_monotonic@tok () Term)
; </end encoding let pure_wp_monotonic>

; <Start encoding let pure_wp>
(declare-fun Prims.pure_wp (Term) Term)

(declare-fun Prims.pure_wp@tok () Term)
(declare-fun Tm_refine_15e0beb75f7033bad5fae236999feebe (Term) Term)
; </end encoding let pure_wp>

; <Start encoding val Prims.guard_free>
(declare-fun Prims.guard_free (Term) Term)

(declare-fun Prims.guard_free@tok () Term)
; </end encoding val Prims.guard_free>

; <Skipped let pure_return0/>

; <Skipped let pure_bind_wp0/>

; <Skipped let pure_if_then_else0/>

; <Skipped let pure_ite_wp0/>

; <Skipped let pure_stronger/>

; <Skipped let pure_close_wp0/>

; <Skipped let pure_trivial/>

; <Skipped new_effect { Prims.PURE ... }/>

; <Skipped effect Prims.Pure a pre post = Prims.PURE a/>

; <Skipped effect Prims.Admit a = Prims.PURE a/>

; <Skipped let pure_null_wp0/>

; <Skipped effect Prims.Tot a = Prims.PURE a/>

; <Start encoding let pure_assert_wp0>
(declare-fun Prims.pure_assert_wp0 (Term) Term)
(declare-fun Tm_arrow_14bcf5e7fc38d91827ecd9d25d3b3a67 () Term)
(declare-fun Prims.pure_assert_wp0@tok () Term)
; </end encoding let pure_assert_wp0>

; <Start encoding let pure_assume_wp0>
(declare-fun Prims.pure_assume_wp0 (Term) Term)

(declare-fun Prims.pure_assume_wp0@tok () Term)
; </end encoding let pure_assume_wp0>

; <Skipped new_effect { Prims.GHOST ... }/>

; <Skipped let purewp_id/>

; <Skipped sub_effect Prims.PURE ~> Prims.GHOST/>

; <Skipped effect Prims.Ghost a pre post = Prims.GHOST a/>

; <Skipped effect Prims.GTot a = Prims.GHOST a/>

; <Start encoding let op_Equals_Equals_Equals>
(declare-fun Prims.op_Equals_Equals_Equals (Term Term Term Term) Term)
(declare-fun Tm_arrow_7fcb145b23c2ac843afd9b126c4f71a9 () Term)
(declare-fun Prims.op_Equals_Equals_Equals@tok () Term)
; </end encoding let op_Equals_Equals_Equals>

; <Start encoding type Prims.dtuple2>
; Constructor
(declare-fun Prims.dtuple2 (Term Term) Term)
; token
(declare-fun Prims.dtuple2@tok () Term)
; Constructor
(declare-fun Prims.Mkdtuple2 (Term Term Term Term) Term)
; Projector
(declare-fun Prims.Mkdtuple2_a (Term) Term)
; Projector
(declare-fun Prims.Mkdtuple2_b (Term) Term)
; Projector
(declare-fun Prims.Mkdtuple2__1 (Term) Term)
; Projector
(declare-fun Prims.Mkdtuple2__2 (Term) Term)
; data constructor proxy: Prims.Mkdtuple2
(declare-fun Prims.Mkdtuple2@tok () Term)



(declare-fun Tm_arrow_22a50f5c5c9bb74bac4384fb8999be8b () Term)
; <start constructor Prims.dtuple2>
; Discriminator definition
(define-fun is-Prims.dtuple2 ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 258)
  (exists ((@x0 Term) (@x1 Term)) (! (= __@x0 (Prims.dtuple2 @x0 @x1)) :qid is-Prims.dtuple2))))
; </end constructor Prims.dtuple2>
; <start constructor Prims.Mkdtuple2>
; Discriminator definition
(define-fun is-Prims.Mkdtuple2 ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 267)
  (=
   __@x0
   (Prims.Mkdtuple2
    (Prims.Mkdtuple2_a __@x0)
    (Prims.Mkdtuple2_b __@x0)
    (Prims.Mkdtuple2__1 __@x0)
    (Prims.Mkdtuple2__2 __@x0)))))
; </end constructor Prims.Mkdtuple2>
; </end encoding type Prims.dtuple2>

; <Start encoding assume Prims.dtuple2__uu___haseq>

; </end encoding assume Prims.dtuple2__uu___haseq>

; <Start encoding val Prims.uu___is_Mkdtuple2>

(declare-fun Prims.uu___is_Mkdtuple2 (Term Term Term) Term)

(declare-fun Tm_arrow_e6f9f7cb1936ec43b52469e706dcadcc () Term)
(declare-fun Prims.uu___is_Mkdtuple2@tok () Term)
; </end encoding val Prims.uu___is_Mkdtuple2>

; <Skipped let uu___is_Mkdtuple2/>

; <Start encoding val Prims.__proj__Mkdtuple2__item___1>

(declare-fun Prims.__proj__Mkdtuple2__item___1 (Term Term Term) Term)

(declare-fun Tm_arrow_26c013ffba39d4f7eeb4bcc80d2d4e22 () Term)
(declare-fun Prims.__proj__Mkdtuple2__item___1@tok () Term)
; </end encoding val Prims.__proj__Mkdtuple2__item___1>

; <Skipped let __proj__Mkdtuple2__item___1/>

; <Start encoding val Prims.__proj__Mkdtuple2__item___2>

(declare-fun Prims.__proj__Mkdtuple2__item___2 (Term Term Term) Term)

(declare-fun Tm_arrow_870cc7701a0d9a8a2d6fb92427a97d66 () Term)
(declare-fun Prims.__proj__Mkdtuple2__item___2@tok () Term)
; </end encoding val Prims.__proj__Mkdtuple2__item___2>

; <Skipped let __proj__Mkdtuple2__item___2/>

; <Start encoding let l_Exists>

(declare-fun Prims.l_Exists (Term Term) Term)


(declare-fun Prims.l_Exists@tok () Term)


(declare-fun Tm_abs_6ba36691ee58dee85cd144324b083848 (Term Term) Term)
; </end encoding let l_Exists>

; <Start encoding val Prims.int>
(declare-fun Prims.int () Term)
; </end encoding val Prims.int>

; <Start encoding val Prims.op_AmpAmp>
(declare-fun Prims.op_AmpAmp (Term Term) Term)
(declare-fun Prims.op_AmpAmp@tok () Term)
; </end encoding val Prims.op_AmpAmp>

; <Start encoding val Prims.op_BarBar>
(declare-fun Prims.op_BarBar (Term Term) Term)
(declare-fun Prims.op_BarBar@tok () Term)
; </end encoding val Prims.op_BarBar>

; <Start encoding val Prims.op_Negation>
(declare-fun Prims.op_Negation (Term) Term)
(declare-fun Prims.op_Negation@tok () Term)
; </end encoding val Prims.op_Negation>

; <Start encoding val Prims.op_Multiply>
(declare-fun Prims.op_Multiply (Term Term) Term)
(declare-fun Prims.op_Multiply@tok () Term)
; </end encoding val Prims.op_Multiply>

; <Start encoding val Prims.op_Subtraction>
(declare-fun Prims.op_Subtraction (Term Term) Term)
(declare-fun Prims.op_Subtraction@tok () Term)
; </end encoding val Prims.op_Subtraction>

; <Start encoding val Prims.op_Addition>
(declare-fun Prims.op_Addition (Term Term) Term)
(declare-fun Prims.op_Addition@tok () Term)
; </end encoding val Prims.op_Addition>

; <Start encoding val Prims.op_Minus>
(declare-fun Prims.op_Minus (Term) Term)
(declare-fun Prims.op_Minus@tok () Term)
; </end encoding val Prims.op_Minus>

; <Start encoding val Prims.op_LessThanOrEqual>
(declare-fun Prims.op_LessThanOrEqual (Term Term) Term)
(declare-fun Prims.op_LessThanOrEqual@tok () Term)
; </end encoding val Prims.op_LessThanOrEqual>

; <Start encoding val Prims.op_GreaterThan>
(declare-fun Prims.op_GreaterThan (Term Term) Term)
(declare-fun Prims.op_GreaterThan@tok () Term)
; </end encoding val Prims.op_GreaterThan>

; <Start encoding val Prims.op_GreaterThanOrEqual>
(declare-fun Prims.op_GreaterThanOrEqual (Term Term) Term)
(declare-fun Prims.op_GreaterThanOrEqual@tok () Term)
; </end encoding val Prims.op_GreaterThanOrEqual>

; <Start encoding val Prims.op_LessThan>
(declare-fun Prims.op_LessThan (Term Term) Term)
(declare-fun Prims.op_LessThan@tok () Term)
; </end encoding val Prims.op_LessThan>

; <Start encoding val Prims.op_Equality>
(declare-fun Prims.op_Equality (Term Term Term) Term)
(declare-fun Prims.op_Equality@tok () Term)
; </end encoding val Prims.op_Equality>

; <Start encoding val Prims.op_disEquality>
(declare-fun Prims.op_disEquality (Term Term Term) Term)
(declare-fun Prims.op_disEquality@tok () Term)
; </end encoding val Prims.op_disEquality>

; <Start encoding val Prims.exn>
(declare-fun Prims.exn () Term)
; </end encoding val Prims.exn>

; <Start encoding val Prims.strcat>
(declare-fun Prims.strcat (Term Term) Term)
(declare-fun Tm_arrow_b66cecec1d56111347abe61e89557dd1 () Term)
(declare-fun Prims.strcat@tok () Term)
; </end encoding val Prims.strcat>

; <Skipped let op_Hat/>

; <Start encoding type Prims.list>
; Constructor
(declare-fun Prims.list (Term) Term)
; token
(declare-fun Prims.list@tok () Term)
; Constructor
(declare-fun Prims.Nil (Term) Term)
; Projector
(declare-fun Prims.Nil_a (Term) Term)
; data constructor proxy: Prims.Nil
(declare-fun Prims.Nil@tok () Term)
; Constructor
(declare-fun Prims.Cons (Term Term Term) Term)
; Projector
(declare-fun Prims.Cons_a (Term) Term)
; Projector
(declare-fun Prims.Cons_hd (Term) Term)
; Projector
(declare-fun Prims.Cons_tl (Term) Term)
; data constructor proxy: Prims.Cons
(declare-fun Prims.Cons@tok () Term)
(declare-fun Tm_arrow_3864bd5fbb999b4fe4487408df9b3401 () Term)
(declare-fun Tm_arrow_02c072760cbad0f5a4706f6cffab6c94 () Term)
; <start constructor Prims.list>
; Discriminator definition
(define-fun is-Prims.list ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 313)
  (exists ((@x0 Term)) (! (= __@x0 (Prims.list @x0)) :qid is-Prims.list))))
; </end constructor Prims.list>
; <start constructor Prims.Nil>
; Discriminator definition
(define-fun is-Prims.Nil ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0) 320) (= __@x0 (Prims.Nil (Prims.Nil_a __@x0)))))
; </end constructor Prims.Nil>
; <start constructor Prims.Cons>
; Discriminator definition
(define-fun is-Prims.Cons ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 325)
  (= __@x0 (Prims.Cons (Prims.Cons_a __@x0) (Prims.Cons_hd __@x0) (Prims.Cons_tl __@x0)))))
; </end constructor Prims.Cons>
; </end encoding type Prims.list>

; <Start encoding assume Prims.list__uu___haseq>
; </end encoding assume Prims.list__uu___haseq>

; <Start encoding val Prims.uu___is_Nil>
(declare-fun Prims.uu___is_Nil (Term Term) Term)
(declare-fun Tm_arrow_606904b0fa72729a20285beb231f9f2e () Term)
(declare-fun Prims.uu___is_Nil@tok () Term)
; </end encoding val Prims.uu___is_Nil>

; <Skipped let uu___is_Nil/>

; <Start encoding val Prims.uu___is_Cons>
(declare-fun Prims.uu___is_Cons (Term Term) Term)

(declare-fun Prims.uu___is_Cons@tok () Term)
; </end encoding val Prims.uu___is_Cons>

; <Skipped let uu___is_Cons/>

; <Start encoding val Prims.__proj__Cons__item__hd>
(declare-fun Tm_refine_7aac12c24449a22c34d98a0ea8ed4a32 (Term) Term)
(declare-fun Prims.__proj__Cons__item__hd (Term Term) Term)

(declare-fun Tm_arrow_27c3547831737e5a63950f3d18bf3d22 () Term)
(declare-fun Prims.__proj__Cons__item__hd@tok () Term)
; </end encoding val Prims.__proj__Cons__item__hd>

; <Skipped let __proj__Cons__item__hd/>

; <Start encoding val Prims.__proj__Cons__item__tl>

(declare-fun Prims.__proj__Cons__item__tl (Term Term) Term)

(declare-fun Tm_arrow_4e740085106d54d8b48ffe3c6c20ef21 () Term)
(declare-fun Prims.__proj__Cons__item__tl@tok () Term)
; </end encoding val Prims.__proj__Cons__item__tl>

; <Skipped let __proj__Cons__item__tl/>

; <Skipped effect Prims.M a = a/>

; <Start encoding let returnM>
(declare-fun Prims.returnM (Term Term) Term)
(declare-fun Tm_arrow_99724436653747ac6f5a6a00c64ff8bc () Term)
(declare-fun Prims.returnM@tok () Term)
; </end encoding let returnM>

; <Skipped let as_requires/>

; <Skipped let as_ensures/>

; <Start encoding val Prims._assume>
(declare-fun Prims._assume (Term) Term)
(declare-fun Non_total_Tm_arrow_724d0dab46b8b51a1bb19d329f7fc4b2 () Term)
(declare-fun Prims._assume@tok () Term)
; </end encoding val Prims._assume>

; <Start encoding val Prims.admit>
; Uninterpreted function symbol for impure function
(declare-fun Prims.admit (Term Term) Term)
; Uninterpreted name for impure function
(declare-fun Prims.admit@tok () Term)
; </end encoding val Prims.admit>

; <Start encoding val Prims.magic>
(declare-fun Prims.magic (Term Term) Term)
(declare-fun Tm_arrow_f5df98ce82fbcebbbdb844c958bee4fb () Term)
(declare-fun Prims.magic@tok () Term)
; </end encoding val Prims.magic>

; <Start encoding let unsafe_coerce>
(declare-fun Prims.unsafe_coerce (Term Term Term) Term)
(declare-fun Tm_arrow_443ab41008720460b7a09e280558a60f () Term)
(declare-fun Prims.unsafe_coerce@tok () Term)
; </end encoding let unsafe_coerce>

; <Start encoding val Prims.admitP>
(declare-fun Prims.admitP (Term) Term)

(declare-fun Prims.admitP@tok () Term)
; </end encoding val Prims.admitP>

; <Skipped val Prims._assert/>

; <Start encoding let _assert>
(declare-fun Prims._assert (Term) Term)
(declare-fun Non_total_Tm_arrow_bb2d1b4bdb07c87bf5990ad3e5fd8642 () Term)
(declare-fun Prims._assert@tok () Term)
; </end encoding let _assert>

; <Skipped val Prims.cut/>

; <Start encoding let cut>
(declare-fun Prims.cut (Term) Term)

(declare-fun Prims.cut@tok () Term)
; </end encoding let cut>

; <Start encoding let nat>
(declare-fun Prims.nat () Term)
(declare-fun Tm_refine_542f9d4f129664613f2483a6c88bc7c2 () Term)
; </end encoding let nat>

; <Start encoding let pos>
(declare-fun Prims.pos () Term)
(declare-fun Tm_refine_774ba3f728d91ead8ef40be66c9802e5 () Term)
; </end encoding let pos>

; <Start encoding let nonzero>
(declare-fun Prims.nonzero () Term)
(declare-fun Tm_refine_0766302b68bb44ab7aff8c4d8be0b46f () Term)
; </end encoding let nonzero>

; <Start encoding val Prims.op_Modulus>
(declare-fun Prims.op_Modulus (Term Term) Term)
(declare-fun Prims.op_Modulus@tok () Term)
; </end encoding val Prims.op_Modulus>

; <Start encoding val Prims.op_Division>
(declare-fun Prims.op_Division (Term Term) Term)
(declare-fun Prims.op_Division@tok () Term)
; </end encoding val Prims.op_Division>

; <Start encoding let rec pow2>
; Fuel-instrumented function name
(declare-fun Prims.pow2.fuel_instrumented (Fuel Term) Term)
; Token for fuel-instrumented partial applications
(declare-fun Prims.pow2.fuel_instrumented_token () Term)
(declare-fun Prims.pow2 (Term) Term)
(declare-fun Prims.pow2@tok () Term)
(declare-fun Tm_arrow_c331a0e032e021e1eaa359b3983de4f2 () Term)
; </end encoding let rec pow2>

; <Start encoding let min>
(declare-fun Prims.min (Term Term) Term)
(declare-fun Tm_arrow_47fc285d7b44e13bcb7e420cbfc55623 () Term)
(declare-fun Prims.min@tok () Term)
; </end encoding let min>

; <Start encoding let abs>
(declare-fun Prims.abs (Term) Term)
(declare-fun Tm_arrow_35447810753695c4fe25c93af1251992 () Term)
(declare-fun Prims.abs@tok () Term)
; </end encoding let abs>

; <Start encoding val Prims.string_of_bool>
(declare-fun Prims.string_of_bool (Term) Term)
(declare-fun Tm_arrow_e86b54405c2a58719f5e8112efd48c09 () Term)
(declare-fun Prims.string_of_bool@tok () Term)
; </end encoding val Prims.string_of_bool>

; <Start encoding val Prims.string_of_int>
(declare-fun Prims.string_of_int (Term) Term)
(declare-fun Tm_arrow_2bc066ec63734c94a3c008e1e72cae2b () Term)
(declare-fun Prims.string_of_int@tok () Term)
; </end encoding val Prims.string_of_int>

; <Start encoding let __cache_version_number__>
(declare-fun Prims.__cache_version_number__ () Term)
; </end encoding let __cache_version_number__>

; End Externals for module Prims
; Externals for interface FStar.Attributes
; <Start encoding type FStar.Attributes.__internal_ocaml_attributes>
; Constructor
(declare-fun FStar.Attributes.__internal_ocaml_attributes () Term)
; Constructor
(declare-fun FStar.Attributes.PpxDerivingShow () Term)
; data constructor proxy: FStar.Attributes.PpxDerivingShow
(declare-fun FStar.Attributes.PpxDerivingShow@tok () Term)
; Constructor
(declare-fun FStar.Attributes.PpxDerivingShowConstant (Term) Term)
; Projector
(declare-fun FStar.Attributes.PpxDerivingShowConstant__0 (Term) Term)
; data constructor proxy: FStar.Attributes.PpxDerivingShowConstant
(declare-fun FStar.Attributes.PpxDerivingShowConstant@tok () Term)
; Constructor
(declare-fun FStar.Attributes.PpxDerivingYoJson () Term)
; data constructor proxy: FStar.Attributes.PpxDerivingYoJson
(declare-fun FStar.Attributes.PpxDerivingYoJson@tok () Term)
; Constructor
(declare-fun FStar.Attributes.CInline () Term)
; data constructor proxy: FStar.Attributes.CInline
(declare-fun FStar.Attributes.CInline@tok () Term)
; Constructor
(declare-fun FStar.Attributes.Substitute () Term)
; data constructor proxy: FStar.Attributes.Substitute
(declare-fun FStar.Attributes.Substitute@tok () Term)
; Constructor
(declare-fun FStar.Attributes.Gc () Term)
; data constructor proxy: FStar.Attributes.Gc
(declare-fun FStar.Attributes.Gc@tok () Term)
; Constructor
(declare-fun FStar.Attributes.Comment (Term) Term)
; Projector
(declare-fun FStar.Attributes.Comment__0 (Term) Term)
; data constructor proxy: FStar.Attributes.Comment
(declare-fun FStar.Attributes.Comment@tok () Term)
; Constructor
(declare-fun FStar.Attributes.CPrologue (Term) Term)
; Projector
(declare-fun FStar.Attributes.CPrologue__0 (Term) Term)
; data constructor proxy: FStar.Attributes.CPrologue
(declare-fun FStar.Attributes.CPrologue@tok () Term)
; Constructor
(declare-fun FStar.Attributes.CEpilogue (Term) Term)
; Projector
(declare-fun FStar.Attributes.CEpilogue__0 (Term) Term)
; data constructor proxy: FStar.Attributes.CEpilogue
(declare-fun FStar.Attributes.CEpilogue@tok () Term)
; Constructor
(declare-fun FStar.Attributes.CConst (Term) Term)
; Projector
(declare-fun FStar.Attributes.CConst__0 (Term) Term)
; data constructor proxy: FStar.Attributes.CConst
(declare-fun FStar.Attributes.CConst@tok () Term)
; Constructor
(declare-fun FStar.Attributes.CCConv (Term) Term)
; Projector
(declare-fun FStar.Attributes.CCConv__0 (Term) Term)
; data constructor proxy: FStar.Attributes.CCConv
(declare-fun FStar.Attributes.CCConv@tok () Term)
; Constructor
(declare-fun FStar.Attributes.CAbstractStruct () Term)
; data constructor proxy: FStar.Attributes.CAbstractStruct
(declare-fun FStar.Attributes.CAbstractStruct@tok () Term)
; Constructor
(declare-fun FStar.Attributes.CIfDef () Term)
; data constructor proxy: FStar.Attributes.CIfDef
(declare-fun FStar.Attributes.CIfDef@tok () Term)
; Constructor
(declare-fun FStar.Attributes.CMacro () Term)
; data constructor proxy: FStar.Attributes.CMacro
(declare-fun FStar.Attributes.CMacro@tok () Term)
; Constructor
(declare-fun FStar.Attributes.CNoInline () Term)
; data constructor proxy: FStar.Attributes.CNoInline
(declare-fun FStar.Attributes.CNoInline@tok () Term)
(declare-fun Tm_arrow_4df7afdecd30bc8ccabe3b1c6376b54b () Term)





; <start constructor FStar.Attributes.__internal_ocaml_attributes>
; Discriminator definition
(define-fun is-FStar.Attributes.__internal_ocaml_attributes ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0) 101) (= __@x0 FStar.Attributes.__internal_ocaml_attributes)))
; </end constructor FStar.Attributes.__internal_ocaml_attributes>
; <start constructor FStar.Attributes.PpxDerivingShow>
; Discriminator definition
(define-fun is-FStar.Attributes.PpxDerivingShow ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0) 107) (= __@x0 FStar.Attributes.PpxDerivingShow)))
; </end constructor FStar.Attributes.PpxDerivingShow>
; <start constructor FStar.Attributes.PpxDerivingShowConstant>
; Discriminator definition
(define-fun is-FStar.Attributes.PpxDerivingShowConstant ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 109)
  (=
   __@x0
   (FStar.Attributes.PpxDerivingShowConstant (FStar.Attributes.PpxDerivingShowConstant__0 __@x0)))))
; </end constructor FStar.Attributes.PpxDerivingShowConstant>
; <start constructor FStar.Attributes.PpxDerivingYoJson>
; Discriminator definition
(define-fun is-FStar.Attributes.PpxDerivingYoJson ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0) 114) (= __@x0 FStar.Attributes.PpxDerivingYoJson)))
; </end constructor FStar.Attributes.PpxDerivingYoJson>
; <start constructor FStar.Attributes.CInline>
; Discriminator definition
(define-fun is-FStar.Attributes.CInline ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0) 116) (= __@x0 FStar.Attributes.CInline)))
; </end constructor FStar.Attributes.CInline>
; <start constructor FStar.Attributes.Substitute>
; Discriminator definition
(define-fun is-FStar.Attributes.Substitute ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0) 118) (= __@x0 FStar.Attributes.Substitute)))
; </end constructor FStar.Attributes.Substitute>
; <start constructor FStar.Attributes.Gc>
; Discriminator definition
(define-fun is-FStar.Attributes.Gc ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0) 120) (= __@x0 FStar.Attributes.Gc)))
; </end constructor FStar.Attributes.Gc>
; <start constructor FStar.Attributes.Comment>
; Discriminator definition
(define-fun is-FStar.Attributes.Comment ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 122)
  (= __@x0 (FStar.Attributes.Comment (FStar.Attributes.Comment__0 __@x0)))))
; </end constructor FStar.Attributes.Comment>
; <start constructor FStar.Attributes.CPrologue>
; Discriminator definition
(define-fun is-FStar.Attributes.CPrologue ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 127)
  (= __@x0 (FStar.Attributes.CPrologue (FStar.Attributes.CPrologue__0 __@x0)))))
; </end constructor FStar.Attributes.CPrologue>
; <start constructor FStar.Attributes.CEpilogue>
; Discriminator definition
(define-fun is-FStar.Attributes.CEpilogue ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 132)
  (= __@x0 (FStar.Attributes.CEpilogue (FStar.Attributes.CEpilogue__0 __@x0)))))
; </end constructor FStar.Attributes.CEpilogue>
; <start constructor FStar.Attributes.CConst>
; Discriminator definition
(define-fun is-FStar.Attributes.CConst ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 137)
  (= __@x0 (FStar.Attributes.CConst (FStar.Attributes.CConst__0 __@x0)))))
; </end constructor FStar.Attributes.CConst>
; <start constructor FStar.Attributes.CCConv>
; Discriminator definition
(define-fun is-FStar.Attributes.CCConv ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 142)
  (= __@x0 (FStar.Attributes.CCConv (FStar.Attributes.CCConv__0 __@x0)))))
; </end constructor FStar.Attributes.CCConv>
; <start constructor FStar.Attributes.CAbstractStruct>
; Discriminator definition
(define-fun is-FStar.Attributes.CAbstractStruct ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0) 147) (= __@x0 FStar.Attributes.CAbstractStruct)))
; </end constructor FStar.Attributes.CAbstractStruct>
; <start constructor FStar.Attributes.CIfDef>
; Discriminator definition
(define-fun is-FStar.Attributes.CIfDef ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0) 149) (= __@x0 FStar.Attributes.CIfDef)))
; </end constructor FStar.Attributes.CIfDef>
; <start constructor FStar.Attributes.CMacro>
; Discriminator definition
(define-fun is-FStar.Attributes.CMacro ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0) 151) (= __@x0 FStar.Attributes.CMacro)))
; </end constructor FStar.Attributes.CMacro>
; <start constructor FStar.Attributes.CNoInline>
; Discriminator definition
(define-fun is-FStar.Attributes.CNoInline ((__@x0 Term)) Bool
 (and (= (Term_constr_id __@x0) 153) (= __@x0 FStar.Attributes.CNoInline)))
; </end constructor FStar.Attributes.CNoInline>
; </end encoding type FStar.Attributes.__internal_ocaml_attributes>

; <Start encoding assume FStar.Attributes.__internal_ocaml_attributes__uu___haseq>
; </end encoding assume FStar.Attributes.__internal_ocaml_attributes__uu___haseq>

; <Start encoding val FStar.Attributes.uu___is_PpxDerivingShow>
(declare-fun FStar.Attributes.uu___is_PpxDerivingShow (Term) Term)
(declare-fun Tm_arrow_81301e6aabb96c573cb5df06bd782860 () Term)
(declare-fun FStar.Attributes.uu___is_PpxDerivingShow@tok () Term)
; </end encoding val FStar.Attributes.uu___is_PpxDerivingShow>

; <Skipped let uu___is_PpxDerivingShow/>

; <Start encoding val FStar.Attributes.uu___is_PpxDerivingShowConstant>
(declare-fun FStar.Attributes.uu___is_PpxDerivingShowConstant (Term) Term)

(declare-fun FStar.Attributes.uu___is_PpxDerivingShowConstant@tok () Term)
; </end encoding val FStar.Attributes.uu___is_PpxDerivingShowConstant>

; <Skipped let uu___is_PpxDerivingShowConstant/>

; <Start encoding val FStar.Attributes.__proj__PpxDerivingShowConstant__item___0>
(declare-fun Tm_refine_bc20f546043cbc577e051a381f558945 () Term)
(declare-fun FStar.Attributes.__proj__PpxDerivingShowConstant__item___0 (Term) Term)

(declare-fun Tm_arrow_90334ab3c9f741c38d4dd8f37f8aea7f () Term)
(declare-fun FStar.Attributes.__proj__PpxDerivingShowConstant__item___0@tok () Term)
; </end encoding val FStar.Attributes.__proj__PpxDerivingShowConstant__item___0>

; <Skipped let __proj__PpxDerivingShowConstant__item___0/>

; <Start encoding val FStar.Attributes.uu___is_PpxDerivingYoJson>
(declare-fun FStar.Attributes.uu___is_PpxDerivingYoJson (Term) Term)

(declare-fun FStar.Attributes.uu___is_PpxDerivingYoJson@tok () Term)
; </end encoding val FStar.Attributes.uu___is_PpxDerivingYoJson>

; <Skipped let uu___is_PpxDerivingYoJson/>

; <Start encoding val FStar.Attributes.uu___is_CInline>
(declare-fun FStar.Attributes.uu___is_CInline (Term) Term)

(declare-fun FStar.Attributes.uu___is_CInline@tok () Term)
; </end encoding val FStar.Attributes.uu___is_CInline>

; <Skipped let uu___is_CInline/>

; <Start encoding val FStar.Attributes.uu___is_Substitute>
(declare-fun FStar.Attributes.uu___is_Substitute (Term) Term)

(declare-fun FStar.Attributes.uu___is_Substitute@tok () Term)
; </end encoding val FStar.Attributes.uu___is_Substitute>

; <Skipped let uu___is_Substitute/>

; <Start encoding val FStar.Attributes.uu___is_Gc>
(declare-fun FStar.Attributes.uu___is_Gc (Term) Term)

(declare-fun FStar.Attributes.uu___is_Gc@tok () Term)
; </end encoding val FStar.Attributes.uu___is_Gc>

; <Skipped let uu___is_Gc/>

; <Start encoding val FStar.Attributes.uu___is_Comment>
(declare-fun FStar.Attributes.uu___is_Comment (Term) Term)

(declare-fun FStar.Attributes.uu___is_Comment@tok () Term)
; </end encoding val FStar.Attributes.uu___is_Comment>

; <Skipped let uu___is_Comment/>

; <Start encoding val FStar.Attributes.__proj__Comment__item___0>
(declare-fun Tm_refine_65d8dd8d83843b4091d0eed7b95619fc () Term)
(declare-fun FStar.Attributes.__proj__Comment__item___0 (Term) Term)

(declare-fun Tm_arrow_1c85ef3e94af845bc9633317c687d94b () Term)
(declare-fun FStar.Attributes.__proj__Comment__item___0@tok () Term)
; </end encoding val FStar.Attributes.__proj__Comment__item___0>

; <Skipped let __proj__Comment__item___0/>

; <Start encoding val FStar.Attributes.uu___is_CPrologue>
(declare-fun FStar.Attributes.uu___is_CPrologue (Term) Term)

(declare-fun FStar.Attributes.uu___is_CPrologue@tok () Term)
; </end encoding val FStar.Attributes.uu___is_CPrologue>

; <Skipped let uu___is_CPrologue/>

; <Start encoding val FStar.Attributes.__proj__CPrologue__item___0>
(declare-fun Tm_refine_0175e351cf87242d4c1ffd69c118281d () Term)
(declare-fun FStar.Attributes.__proj__CPrologue__item___0 (Term) Term)

(declare-fun Tm_arrow_11884c7c6f4c81c3c2668702db5f5528 () Term)
(declare-fun FStar.Attributes.__proj__CPrologue__item___0@tok () Term)
; </end encoding val FStar.Attributes.__proj__CPrologue__item___0>

; <Skipped let __proj__CPrologue__item___0/>

; <Start encoding val FStar.Attributes.uu___is_CEpilogue>
(declare-fun FStar.Attributes.uu___is_CEpilogue (Term) Term)

(declare-fun FStar.Attributes.uu___is_CEpilogue@tok () Term)
; </end encoding val FStar.Attributes.uu___is_CEpilogue>

; <Skipped let uu___is_CEpilogue/>

; <Start encoding val FStar.Attributes.__proj__CEpilogue__item___0>
(declare-fun Tm_refine_2ef021290f2c4525f88b861d7725ce44 () Term)
(declare-fun FStar.Attributes.__proj__CEpilogue__item___0 (Term) Term)

(declare-fun Tm_arrow_262e88f0b9ff33dbbfa189b220e3fb6a () Term)
(declare-fun FStar.Attributes.__proj__CEpilogue__item___0@tok () Term)
; </end encoding val FStar.Attributes.__proj__CEpilogue__item___0>

; <Skipped let __proj__CEpilogue__item___0/>

; <Start encoding val FStar.Attributes.uu___is_CConst>
(declare-fun FStar.Attributes.uu___is_CConst (Term) Term)

(declare-fun FStar.Attributes.uu___is_CConst@tok () Term)
; </end encoding val FStar.Attributes.uu___is_CConst>

; <Skipped let uu___is_CConst/>

; <Start encoding val FStar.Attributes.__proj__CConst__item___0>
(declare-fun Tm_refine_170d8c8be9250274534e64f6d4fd41a0 () Term)
(declare-fun FStar.Attributes.__proj__CConst__item___0 (Term) Term)

(declare-fun Tm_arrow_e56ab9a22f1e0f5e4d9b27a10a6d6975 () Term)
(declare-fun FStar.Attributes.__proj__CConst__item___0@tok () Term)
; </end encoding val FStar.Attributes.__proj__CConst__item___0>

; <Skipped let __proj__CConst__item___0/>

; <Start encoding val FStar.Attributes.uu___is_CCConv>
(declare-fun FStar.Attributes.uu___is_CCConv (Term) Term)

(declare-fun FStar.Attributes.uu___is_CCConv@tok () Term)
; </end encoding val FStar.Attributes.uu___is_CCConv>

; <Skipped let uu___is_CCConv/>

; <Start encoding val FStar.Attributes.__proj__CCConv__item___0>
(declare-fun Tm_refine_446d9c4f0bd59e4fd55eae5447f4bd0d () Term)
(declare-fun FStar.Attributes.__proj__CCConv__item___0 (Term) Term)

(declare-fun Tm_arrow_fc29f768abe11db1d2b28f00b86486f8 () Term)
(declare-fun FStar.Attributes.__proj__CCConv__item___0@tok () Term)
; </end encoding val FStar.Attributes.__proj__CCConv__item___0>

; <Skipped let __proj__CCConv__item___0/>

; <Start encoding val FStar.Attributes.uu___is_CAbstractStruct>
(declare-fun FStar.Attributes.uu___is_CAbstractStruct (Term) Term)

(declare-fun FStar.Attributes.uu___is_CAbstractStruct@tok () Term)
; </end encoding val FStar.Attributes.uu___is_CAbstractStruct>

; <Skipped let uu___is_CAbstractStruct/>

; <Start encoding val FStar.Attributes.uu___is_CIfDef>
(declare-fun FStar.Attributes.uu___is_CIfDef (Term) Term)

(declare-fun FStar.Attributes.uu___is_CIfDef@tok () Term)
; </end encoding val FStar.Attributes.uu___is_CIfDef>

; <Skipped let uu___is_CIfDef/>

; <Start encoding val FStar.Attributes.uu___is_CMacro>
(declare-fun FStar.Attributes.uu___is_CMacro (Term) Term)

(declare-fun FStar.Attributes.uu___is_CMacro@tok () Term)
; </end encoding val FStar.Attributes.uu___is_CMacro>

; <Skipped let uu___is_CMacro/>

; <Start encoding val FStar.Attributes.uu___is_CNoInline>
(declare-fun FStar.Attributes.uu___is_CNoInline (Term) Term)

(declare-fun FStar.Attributes.uu___is_CNoInline@tok () Term)
; </end encoding val FStar.Attributes.uu___is_CNoInline>

; <Skipped let uu___is_CNoInline/>

; <Start encoding val FStar.Attributes.inline_let>
(declare-fun FStar.Attributes.inline_let (Dummy_sort) Term)
; </end encoding val FStar.Attributes.inline_let>

; <Start encoding val FStar.Attributes.inline_let_vc>
(declare-fun FStar.Attributes.inline_let_vc (Dummy_sort) Term)
; </end encoding val FStar.Attributes.inline_let_vc>

; <Start encoding val FStar.Attributes.no_inline_let>
(declare-fun FStar.Attributes.no_inline_let (Dummy_sort) Term)
; </end encoding val FStar.Attributes.no_inline_let>

; <Start encoding val FStar.Attributes.rename_let>
(declare-fun FStar.Attributes.rename_let (Term) Term)

(declare-fun FStar.Attributes.rename_let@tok () Term)
; </end encoding val FStar.Attributes.rename_let>

; <Start encoding val FStar.Attributes.plugin>
(declare-fun FStar.Attributes.plugin (Term) Term)
(declare-fun Tm_arrow_f12575a0ee171a8be16a63e3359708f8 () Term)
(declare-fun FStar.Attributes.plugin@tok () Term)
; </end encoding val FStar.Attributes.plugin>

; <Start encoding val FStar.Attributes.tcnorm>
(declare-fun FStar.Attributes.tcnorm (Dummy_sort) Term)
; </end encoding val FStar.Attributes.tcnorm>

; <Start encoding val FStar.Attributes.dm4f_bind_range>
(declare-fun FStar.Attributes.dm4f_bind_range (Dummy_sort) Term)
; </end encoding val FStar.Attributes.dm4f_bind_range>

; <Start encoding val FStar.Attributes.must_erase_for_extraction>
(declare-fun FStar.Attributes.must_erase_for_extraction (Dummy_sort) Term)
; </end encoding val FStar.Attributes.must_erase_for_extraction>

; <Start encoding val FStar.Attributes.expect_failure>
(declare-fun FStar.Attributes.expect_failure (Term) Term)
(declare-fun Tm_arrow_555d62757eeaf90340982fcdf25f6704 () Term)
(declare-fun FStar.Attributes.expect_failure@tok () Term)
; </end encoding val FStar.Attributes.expect_failure>

; <Start encoding val FStar.Attributes.expect_lax_failure>
(declare-fun FStar.Attributes.expect_lax_failure (Term) Term)

(declare-fun FStar.Attributes.expect_lax_failure@tok () Term)
; </end encoding val FStar.Attributes.expect_lax_failure>

; <Start encoding val FStar.Attributes.tcdecltime>
(declare-fun FStar.Attributes.tcdecltime (Dummy_sort) Term)
; </end encoding val FStar.Attributes.tcdecltime>

; <Start encoding val FStar.Attributes.unifier_hint_injective>
(declare-fun FStar.Attributes.unifier_hint_injective (Dummy_sort) Term)
; </end encoding val FStar.Attributes.unifier_hint_injective>

; <Start encoding val FStar.Attributes.strict_on_arguments>
(declare-fun FStar.Attributes.strict_on_arguments (Term) Term)

(declare-fun FStar.Attributes.strict_on_arguments@tok () Term)
; </end encoding val FStar.Attributes.strict_on_arguments>

; <Start encoding val FStar.Attributes.resolve_implicits>
(declare-fun FStar.Attributes.resolve_implicits (Dummy_sort) Term)
; </end encoding val FStar.Attributes.resolve_implicits>

; <Start encoding val FStar.Attributes.override_resolve_implicits_handler>
(declare-fun FStar.Attributes.override_resolve_implicits_handler (Term Term Term) Term)
(declare-fun Tm_arrow_93e6548cfc250f7cc25301579d62a018 () Term)
(declare-fun FStar.Attributes.override_resolve_implicits_handler@tok () Term)
; </end encoding val FStar.Attributes.override_resolve_implicits_handler>

; <Start encoding val FStar.Attributes.handle_smt_goals>
(declare-fun FStar.Attributes.handle_smt_goals (Dummy_sort) Term)
; </end encoding val FStar.Attributes.handle_smt_goals>

; <Start encoding val FStar.Attributes.erasable>
(declare-fun FStar.Attributes.erasable (Dummy_sort) Term)
; </end encoding val FStar.Attributes.erasable>

; <Start encoding val FStar.Attributes.commute_nested_matches>
(declare-fun FStar.Attributes.commute_nested_matches (Dummy_sort) Term)
; </end encoding val FStar.Attributes.commute_nested_matches>

; <Start encoding val FStar.Attributes.noextract_to>
(declare-fun FStar.Attributes.noextract_to (Term) Term)

(declare-fun FStar.Attributes.noextract_to@tok () Term)
; </end encoding val FStar.Attributes.noextract_to>

; <Start encoding val FStar.Attributes.ite_soundness_by>
(declare-fun FStar.Attributes.ite_soundness_by (Term) Term)
(declare-fun Tm_arrow_0c55530a575bf8e94add46ffb548393c () Term)
(declare-fun FStar.Attributes.ite_soundness_by@tok () Term)
; </end encoding val FStar.Attributes.ite_soundness_by>

; <Start encoding val FStar.Attributes.default_effect>
(declare-fun FStar.Attributes.default_effect (Term) Term)

(declare-fun FStar.Attributes.default_effect@tok () Term)
; </end encoding val FStar.Attributes.default_effect>

; <Start encoding val FStar.Attributes.top_level_effect>
(declare-fun FStar.Attributes.top_level_effect (Term) Term)

(declare-fun FStar.Attributes.top_level_effect@tok () Term)
; </end encoding val FStar.Attributes.top_level_effect>

; <Start encoding val FStar.Attributes.effect_param>
(declare-fun FStar.Attributes.effect_param (Dummy_sort) Term)
; </end encoding val FStar.Attributes.effect_param>

; <Start encoding val FStar.Attributes.bind_has_range_args>
(declare-fun FStar.Attributes.bind_has_range_args (Dummy_sort) Term)
; </end encoding val FStar.Attributes.bind_has_range_args>

; <Start encoding val FStar.Attributes.primitive_extraction>
(declare-fun FStar.Attributes.primitive_extraction (Dummy_sort) Term)
; </end encoding val FStar.Attributes.primitive_extraction>

; <Start encoding val FStar.Attributes.extract_as_impure_effect>
(declare-fun FStar.Attributes.extract_as_impure_effect (Dummy_sort) Term)
; </end encoding val FStar.Attributes.extract_as_impure_effect>

; <Start encoding val FStar.Attributes.strictly_positive>
(declare-fun FStar.Attributes.strictly_positive (Dummy_sort) Term)
; </end encoding val FStar.Attributes.strictly_positive>

; <Start encoding val FStar.Attributes.unused>
(declare-fun FStar.Attributes.unused (Dummy_sort) Term)
; </end encoding val FStar.Attributes.unused>

; <Start encoding val FStar.Attributes.no_auto_projectors>
(declare-fun FStar.Attributes.no_auto_projectors (Dummy_sort) Term)
; </end encoding val FStar.Attributes.no_auto_projectors>

; <Start encoding val FStar.Attributes.no_auto_projectors_decls>
(declare-fun FStar.Attributes.no_auto_projectors_decls (Dummy_sort) Term)
; </end encoding val FStar.Attributes.no_auto_projectors_decls>

; <Start encoding val FStar.Attributes.no_subtyping>
(declare-fun FStar.Attributes.no_subtyping (Dummy_sort) Term)
; </end encoding val FStar.Attributes.no_subtyping>

; <Start encoding val FStar.Attributes.admitted>
(declare-fun FStar.Attributes.admitted (Dummy_sort) Term)
; </end encoding val FStar.Attributes.admitted>

; <Start encoding val FStar.Attributes.admit_termination>
(declare-fun FStar.Attributes.admit_termination (Dummy_sort) Term)
; </end encoding val FStar.Attributes.admit_termination>

; <Start encoding val FStar.Attributes.coercion>
(declare-fun FStar.Attributes.coercion (Dummy_sort) Term)
; </end encoding val FStar.Attributes.coercion>

; <Start encoding val FStar.Attributes.desugar_of_variant_record>
(declare-fun FStar.Attributes.desugar_of_variant_record (Term) Term)

(declare-fun FStar.Attributes.desugar_of_variant_record@tok () Term)
; </end encoding val FStar.Attributes.desugar_of_variant_record>

; <Start encoding val FStar.Attributes.defer_to>
(declare-fun FStar.Attributes.defer_to (Term Term) Term)
(declare-fun Tm_arrow_962476a7eea46a6ffc9b658c6d8fbc71 () Term)
(declare-fun FStar.Attributes.defer_to@tok () Term)
; </end encoding val FStar.Attributes.defer_to>

; End Externals for interface FStar.Attributes
; Externals for interface FStar.NormSteps
; <Start encoding val FStar.NormSteps.norm_step>
(declare-fun FStar.NormSteps.norm_step () Term)
; </end encoding val FStar.NormSteps.norm_step>

; <Start encoding val FStar.NormSteps.simplify>
(declare-fun FStar.NormSteps.simplify (Dummy_sort) Term)
; </end encoding val FStar.NormSteps.simplify>

; <Start encoding val FStar.NormSteps.weak>
(declare-fun FStar.NormSteps.weak (Dummy_sort) Term)
; </end encoding val FStar.NormSteps.weak>

; <Start encoding val FStar.NormSteps.hnf>
(declare-fun FStar.NormSteps.hnf (Dummy_sort) Term)
; </end encoding val FStar.NormSteps.hnf>

; <Start encoding val FStar.NormSteps.primops>
(declare-fun FStar.NormSteps.primops (Dummy_sort) Term)
; </end encoding val FStar.NormSteps.primops>

; <Start encoding val FStar.NormSteps.delta>
(declare-fun FStar.NormSteps.delta (Dummy_sort) Term)
; </end encoding val FStar.NormSteps.delta>

; <Start encoding val FStar.NormSteps.norm_debug>
(declare-fun FStar.NormSteps.norm_debug (Dummy_sort) Term)
; </end encoding val FStar.NormSteps.norm_debug>

; <Start encoding val FStar.NormSteps.zeta>
(declare-fun FStar.NormSteps.zeta (Dummy_sort) Term)
; </end encoding val FStar.NormSteps.zeta>

; <Start encoding val FStar.NormSteps.zeta_full>
(declare-fun FStar.NormSteps.zeta_full (Dummy_sort) Term)
; </end encoding val FStar.NormSteps.zeta_full>

; <Start encoding val FStar.NormSteps.iota>
(declare-fun FStar.NormSteps.iota (Dummy_sort) Term)
; </end encoding val FStar.NormSteps.iota>

; <Start encoding val FStar.NormSteps.nbe>
(declare-fun FStar.NormSteps.nbe (Dummy_sort) Term)
; </end encoding val FStar.NormSteps.nbe>

; <Start encoding val FStar.NormSteps.reify_>
(declare-fun FStar.NormSteps.reify_ (Dummy_sort) Term)
; </end encoding val FStar.NormSteps.reify_>

; <Start encoding val FStar.NormSteps.delta_only>
(declare-fun FStar.NormSteps.delta_only (Term) Term)
(declare-fun Tm_arrow_29d7a35999b647dbf2c0b7f8839c0cb6 () Term)
(declare-fun FStar.NormSteps.delta_only@tok () Term)
; </end encoding val FStar.NormSteps.delta_only>

; <Start encoding val FStar.NormSteps.delta_once>
(declare-fun FStar.NormSteps.delta_once (Term) Term)

(declare-fun FStar.NormSteps.delta_once@tok () Term)
; </end encoding val FStar.NormSteps.delta_once>

; <Start encoding val FStar.NormSteps.delta_fully>
(declare-fun FStar.NormSteps.delta_fully (Term) Term)

(declare-fun FStar.NormSteps.delta_fully@tok () Term)
; </end encoding val FStar.NormSteps.delta_fully>

; <Start encoding val FStar.NormSteps.delta_attr>
(declare-fun FStar.NormSteps.delta_attr (Term) Term)

(declare-fun FStar.NormSteps.delta_attr@tok () Term)
; </end encoding val FStar.NormSteps.delta_attr>

; <Start encoding val FStar.NormSteps.delta_qualifier>
(declare-fun FStar.NormSteps.delta_qualifier (Term) Term)

(declare-fun FStar.NormSteps.delta_qualifier@tok () Term)
; </end encoding val FStar.NormSteps.delta_qualifier>

; <Start encoding val FStar.NormSteps.delta_namespace>
(declare-fun FStar.NormSteps.delta_namespace (Term) Term)

(declare-fun FStar.NormSteps.delta_namespace@tok () Term)
; </end encoding val FStar.NormSteps.delta_namespace>

; <Start encoding val FStar.NormSteps.unmeta>
(declare-fun FStar.NormSteps.unmeta (Dummy_sort) Term)
; </end encoding val FStar.NormSteps.unmeta>

; <Start encoding val FStar.NormSteps.unascribe>
(declare-fun FStar.NormSteps.unascribe (Dummy_sort) Term)
; </end encoding val FStar.NormSteps.unascribe>

; End Externals for interface FStar.NormSteps
; Externals for module FStar.Pervasives.Native
; <Start encoding type FStar.Pervasives.Native.option>
; Constructor
(declare-fun FStar.Pervasives.Native.option (Term) Term)
; token
(declare-fun FStar.Pervasives.Native.option@tok () Term)
; Constructor
(declare-fun FStar.Pervasives.Native.None (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.None_a (Term) Term)
; data constructor proxy: FStar.Pervasives.Native.None
(declare-fun FStar.Pervasives.Native.None@tok () Term)
; Constructor
(declare-fun FStar.Pervasives.Native.Some (Term Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Some_a (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Some_v (Term) Term)
; data constructor proxy: FStar.Pervasives.Native.Some
(declare-fun FStar.Pervasives.Native.Some@tok () Term)
(declare-fun Tm_arrow_48b914114ec9f2f1caadf0f6848a9741 () Term)
(declare-fun Tm_arrow_b93a364b5144c2a5f3e9d1ea7b881752 () Term)
; <start constructor FStar.Pervasives.Native.option>
; Discriminator definition
(define-fun is-FStar.Pervasives.Native.option ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 101)
  (exists ((@x0 Term))
   (! (= __@x0 (FStar.Pervasives.Native.option @x0)) :qid is-FStar.Pervasives.Native.option))))
; </end constructor FStar.Pervasives.Native.option>
; <start constructor FStar.Pervasives.Native.None>
; Discriminator definition
(define-fun is-FStar.Pervasives.Native.None ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 108)
  (= __@x0 (FStar.Pervasives.Native.None (FStar.Pervasives.Native.None_a __@x0)))))
; </end constructor FStar.Pervasives.Native.None>
; <start constructor FStar.Pervasives.Native.Some>
; Discriminator definition
(define-fun is-FStar.Pervasives.Native.Some ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 113)
  (=
   __@x0
   (FStar.Pervasives.Native.Some
    (FStar.Pervasives.Native.Some_a __@x0)
    (FStar.Pervasives.Native.Some_v __@x0)))))
; </end constructor FStar.Pervasives.Native.Some>
; </end encoding type FStar.Pervasives.Native.option>

; <Start encoding assume FStar.Pervasives.Native.option__uu___haseq>
; </end encoding assume FStar.Pervasives.Native.option__uu___haseq>

; <Start encoding val FStar.Pervasives.Native.uu___is_None>
(declare-fun FStar.Pervasives.Native.uu___is_None (Term Term) Term)
(declare-fun Tm_arrow_f1a97bcd6ba9b40d22609b756f183afa () Term)
(declare-fun FStar.Pervasives.Native.uu___is_None@tok () Term)
; </end encoding val FStar.Pervasives.Native.uu___is_None>

; <Skipped let uu___is_None/>

; <Start encoding val FStar.Pervasives.Native.uu___is_Some>
(declare-fun FStar.Pervasives.Native.uu___is_Some (Term Term) Term)

(declare-fun FStar.Pervasives.Native.uu___is_Some@tok () Term)
; </end encoding val FStar.Pervasives.Native.uu___is_Some>

; <Skipped let uu___is_Some/>

; <Start encoding val FStar.Pervasives.Native.__proj__Some__item__v>
(declare-fun Tm_refine_4d5241eb6fe198666a8101195bbd4a2a (Term) Term)
(declare-fun FStar.Pervasives.Native.__proj__Some__item__v (Term Term) Term)

(declare-fun Tm_arrow_1b1398c011ff53e4194fc2ec00c7b411 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Some__item__v@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Some__item__v>

; <Skipped let __proj__Some__item__v/>

; <Start encoding type FStar.Pervasives.Native.tuple2>
; Constructor
(declare-fun FStar.Pervasives.Native.tuple2 (Term Term) Term)
; token
(declare-fun FStar.Pervasives.Native.tuple2@tok () Term)
; Constructor
(declare-fun FStar.Pervasives.Native.Mktuple2 (Term Term Term Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple2__a (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple2__b (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple2__1 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple2__2 (Term) Term)
; data constructor proxy: FStar.Pervasives.Native.Mktuple2
(declare-fun FStar.Pervasives.Native.Mktuple2@tok () Term)
(declare-fun Tm_arrow_4054cc0a51327db54c2ed9ba3376a093 () Term)
; <start constructor FStar.Pervasives.Native.tuple2>
; Discriminator definition
(define-fun is-FStar.Pervasives.Native.tuple2 ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 125)
  (exists ((@x0 Term) (@x1 Term))
   (! (= __@x0 (FStar.Pervasives.Native.tuple2 @x0 @x1)) :qid is-FStar.Pervasives.Native.tuple2))))
; </end constructor FStar.Pervasives.Native.tuple2>
; <start constructor FStar.Pervasives.Native.Mktuple2>
; Discriminator definition
(define-fun is-FStar.Pervasives.Native.Mktuple2 ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 132)
  (=
   __@x0
   (FStar.Pervasives.Native.Mktuple2
    (FStar.Pervasives.Native.Mktuple2__a __@x0)
    (FStar.Pervasives.Native.Mktuple2__b __@x0)
    (FStar.Pervasives.Native.Mktuple2__1 __@x0)
    (FStar.Pervasives.Native.Mktuple2__2 __@x0)))))
; </end constructor FStar.Pervasives.Native.Mktuple2>
; </end encoding type FStar.Pervasives.Native.tuple2>

; <Start encoding assume FStar.Pervasives.Native.tuple2__uu___haseq>
; </end encoding assume FStar.Pervasives.Native.tuple2__uu___haseq>

; <Start encoding val FStar.Pervasives.Native.uu___is_Mktuple2>
(declare-fun FStar.Pervasives.Native.uu___is_Mktuple2 (Term Term Term) Term)
(declare-fun Tm_arrow_eff71eeee4474e017e02350f86f54756 () Term)
(declare-fun FStar.Pervasives.Native.uu___is_Mktuple2@tok () Term)
; </end encoding val FStar.Pervasives.Native.uu___is_Mktuple2>

; <Skipped let uu___is_Mktuple2/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple2__item___1>
(declare-fun FStar.Pervasives.Native.__proj__Mktuple2__item___1 (Term Term Term) Term)
(declare-fun Tm_arrow_b8cce376a4a678a51298a0f3945f25ce () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple2__item___1@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple2__item___1>

; <Skipped let __proj__Mktuple2__item___1/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple2__item___2>
(declare-fun FStar.Pervasives.Native.__proj__Mktuple2__item___2 (Term Term Term) Term)
(declare-fun Tm_arrow_d952d001575ecb20c572af535c88dd2d () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple2__item___2@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple2__item___2>

; <Skipped let __proj__Mktuple2__item___2/>

; <Start encoding let fst>
(declare-fun FStar.Pervasives.Native.fst (Term Term Term) Term)

(declare-fun FStar.Pervasives.Native.fst@tok () Term)
; </end encoding let fst>

; <Start encoding let snd>
(declare-fun FStar.Pervasives.Native.snd (Term Term Term) Term)

(declare-fun FStar.Pervasives.Native.snd@tok () Term)
; </end encoding let snd>

; <Start encoding type FStar.Pervasives.Native.tuple3>
; Constructor
(declare-fun FStar.Pervasives.Native.tuple3 (Term Term Term) Term)
; token
(declare-fun FStar.Pervasives.Native.tuple3@tok () Term)
; Constructor
(declare-fun FStar.Pervasives.Native.Mktuple3 (Term Term Term Term Term Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple3__a (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple3__b (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple3__c (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple3__1 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple3__2 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple3__3 (Term) Term)
; data constructor proxy: FStar.Pervasives.Native.Mktuple3
(declare-fun FStar.Pervasives.Native.Mktuple3@tok () Term)
(declare-fun Tm_arrow_1bedda193f13e939931cf5d46ad84216 () Term)
; <start constructor FStar.Pervasives.Native.tuple3>
; Discriminator definition
(define-fun is-FStar.Pervasives.Native.tuple3 ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 146)
  (exists ((@x0 Term) (@x1 Term) (@x2 Term))
   (! (= __@x0 (FStar.Pervasives.Native.tuple3 @x0 @x1 @x2)) :qid is-FStar.Pervasives.Native.tuple3))))
; </end constructor FStar.Pervasives.Native.tuple3>
; <start constructor FStar.Pervasives.Native.Mktuple3>
; Discriminator definition
(define-fun is-FStar.Pervasives.Native.Mktuple3 ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 153)
  (=
   __@x0
   (FStar.Pervasives.Native.Mktuple3
    (FStar.Pervasives.Native.Mktuple3__a __@x0)
    (FStar.Pervasives.Native.Mktuple3__b __@x0)
    (FStar.Pervasives.Native.Mktuple3__c __@x0)
    (FStar.Pervasives.Native.Mktuple3__1 __@x0)
    (FStar.Pervasives.Native.Mktuple3__2 __@x0)
    (FStar.Pervasives.Native.Mktuple3__3 __@x0)))))
; </end constructor FStar.Pervasives.Native.Mktuple3>
; </end encoding type FStar.Pervasives.Native.tuple3>

; <Start encoding assume FStar.Pervasives.Native.tuple3__uu___haseq>
; </end encoding assume FStar.Pervasives.Native.tuple3__uu___haseq>

; <Start encoding val FStar.Pervasives.Native.uu___is_Mktuple3>
(declare-fun FStar.Pervasives.Native.uu___is_Mktuple3 (Term Term Term Term) Term)
(declare-fun Tm_arrow_f03c6dc5b30146aaca49ed4bf6f332a7 () Term)
(declare-fun FStar.Pervasives.Native.uu___is_Mktuple3@tok () Term)
; </end encoding val FStar.Pervasives.Native.uu___is_Mktuple3>

; <Skipped let uu___is_Mktuple3/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple3__item___1>
(declare-fun FStar.Pervasives.Native.__proj__Mktuple3__item___1 (Term Term Term Term) Term)
(declare-fun Tm_arrow_592c45439d32a71e1933eacb9776c9ed () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple3__item___1@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple3__item___1>

; <Skipped let __proj__Mktuple3__item___1/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple3__item___2>
(declare-fun FStar.Pervasives.Native.__proj__Mktuple3__item___2 (Term Term Term Term) Term)
(declare-fun Tm_arrow_9c9b0c5ac9b0fbfc367f406af296ecab () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple3__item___2@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple3__item___2>

; <Skipped let __proj__Mktuple3__item___2/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple3__item___3>
(declare-fun FStar.Pervasives.Native.__proj__Mktuple3__item___3 (Term Term Term Term) Term)
(declare-fun Tm_arrow_08246a62c9aeca08c44c602ad80e95a4 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple3__item___3@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple3__item___3>

; <Skipped let __proj__Mktuple3__item___3/>

; <Start encoding type FStar.Pervasives.Native.tuple4>
; Constructor
(declare-fun FStar.Pervasives.Native.tuple4 (Term Term Term Term) Term)
; token
(declare-fun FStar.Pervasives.Native.tuple4@tok () Term)
; Constructor
(declare-fun FStar.Pervasives.Native.Mktuple4 (Term Term Term Term Term Term Term Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple4__a (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple4__b (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple4__c (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple4__d (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple4__1 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple4__2 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple4__3 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple4__4 (Term) Term)
; data constructor proxy: FStar.Pervasives.Native.Mktuple4
(declare-fun FStar.Pervasives.Native.Mktuple4@tok () Term)
(declare-fun Tm_arrow_cbe72a10167439fe1ecfaf4fec8fd23f () Term)
; <start constructor FStar.Pervasives.Native.tuple4>
; Discriminator definition
(define-fun is-FStar.Pervasives.Native.tuple4 ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 165)
  (exists ((@x0 Term) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (= __@x0 (FStar.Pervasives.Native.tuple4 @x0 @x1 @x2 @x3))
    :qid is-FStar.Pervasives.Native.tuple4))))
; </end constructor FStar.Pervasives.Native.tuple4>
; <start constructor FStar.Pervasives.Native.Mktuple4>
; Discriminator definition
(define-fun is-FStar.Pervasives.Native.Mktuple4 ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 172)
  (=
   __@x0
   (FStar.Pervasives.Native.Mktuple4
    (FStar.Pervasives.Native.Mktuple4__a __@x0)
    (FStar.Pervasives.Native.Mktuple4__b __@x0)
    (FStar.Pervasives.Native.Mktuple4__c __@x0)
    (FStar.Pervasives.Native.Mktuple4__d __@x0)
    (FStar.Pervasives.Native.Mktuple4__1 __@x0)
    (FStar.Pervasives.Native.Mktuple4__2 __@x0)
    (FStar.Pervasives.Native.Mktuple4__3 __@x0)
    (FStar.Pervasives.Native.Mktuple4__4 __@x0)))))
; </end constructor FStar.Pervasives.Native.Mktuple4>
; </end encoding type FStar.Pervasives.Native.tuple4>

; <Start encoding assume FStar.Pervasives.Native.tuple4__uu___haseq>
; </end encoding assume FStar.Pervasives.Native.tuple4__uu___haseq>

; <Start encoding val FStar.Pervasives.Native.uu___is_Mktuple4>
(declare-fun FStar.Pervasives.Native.uu___is_Mktuple4 (Term Term Term Term Term) Term)
(declare-fun Tm_arrow_4319694c225efa92ce9fad6e9d81f761 () Term)
(declare-fun FStar.Pervasives.Native.uu___is_Mktuple4@tok () Term)
; </end encoding val FStar.Pervasives.Native.uu___is_Mktuple4>

; <Skipped let uu___is_Mktuple4/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple4__item___1>
(declare-fun FStar.Pervasives.Native.__proj__Mktuple4__item___1 (Term Term Term Term Term) Term)
(declare-fun Tm_arrow_382d1e9129053162252ec57e86d46f82 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple4__item___1@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple4__item___1>

; <Skipped let __proj__Mktuple4__item___1/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple4__item___2>
(declare-fun FStar.Pervasives.Native.__proj__Mktuple4__item___2 (Term Term Term Term Term) Term)
(declare-fun Tm_arrow_fffd25e5325d259efa0675ef649c6864 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple4__item___2@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple4__item___2>

; <Skipped let __proj__Mktuple4__item___2/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple4__item___3>
(declare-fun FStar.Pervasives.Native.__proj__Mktuple4__item___3 (Term Term Term Term Term) Term)
(declare-fun Tm_arrow_57b4005e0833f7b396e349ed7cdd1bb2 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple4__item___3@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple4__item___3>

; <Skipped let __proj__Mktuple4__item___3/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple4__item___4>
(declare-fun FStar.Pervasives.Native.__proj__Mktuple4__item___4 (Term Term Term Term Term) Term)
(declare-fun Tm_arrow_9e6c1a63d63f8735645b9898955a2dca () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple4__item___4@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple4__item___4>

; <Skipped let __proj__Mktuple4__item___4/>

; <Start encoding type FStar.Pervasives.Native.tuple5>
; Constructor
(declare-fun FStar.Pervasives.Native.tuple5 (Term Term Term Term Term) Term)
; token
(declare-fun FStar.Pervasives.Native.tuple5@tok () Term)
; Constructor
(declare-fun
 FStar.Pervasives.Native.Mktuple5
 (Term Term Term Term Term Term Term Term Term Term)
 Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple5__a (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple5__b (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple5__c (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple5__d (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple5__e (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple5__1 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple5__2 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple5__3 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple5__4 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple5__5 (Term) Term)
; data constructor proxy: FStar.Pervasives.Native.Mktuple5
(declare-fun FStar.Pervasives.Native.Mktuple5@tok () Term)
(declare-fun Tm_arrow_dd8a078a1b97a81b5089dc3637cc2887 () Term)
; <start constructor FStar.Pervasives.Native.tuple5>
; Discriminator definition
(define-fun is-FStar.Pervasives.Native.tuple5 ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 186)
  (exists ((@x0 Term) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term))
   (! (= __@x0 (FStar.Pervasives.Native.tuple5 @x0 @x1 @x2 @x3 @x4))
    :qid is-FStar.Pervasives.Native.tuple5))))
; </end constructor FStar.Pervasives.Native.tuple5>
; <start constructor FStar.Pervasives.Native.Mktuple5>
; Discriminator definition
(define-fun is-FStar.Pervasives.Native.Mktuple5 ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 193)
  (=
   __@x0
   (FStar.Pervasives.Native.Mktuple5
    (FStar.Pervasives.Native.Mktuple5__a __@x0)
    (FStar.Pervasives.Native.Mktuple5__b __@x0)
    (FStar.Pervasives.Native.Mktuple5__c __@x0)
    (FStar.Pervasives.Native.Mktuple5__d __@x0)
    (FStar.Pervasives.Native.Mktuple5__e __@x0)
    (FStar.Pervasives.Native.Mktuple5__1 __@x0)
    (FStar.Pervasives.Native.Mktuple5__2 __@x0)
    (FStar.Pervasives.Native.Mktuple5__3 __@x0)
    (FStar.Pervasives.Native.Mktuple5__4 __@x0)
    (FStar.Pervasives.Native.Mktuple5__5 __@x0)))))
; </end constructor FStar.Pervasives.Native.Mktuple5>
; </end encoding type FStar.Pervasives.Native.tuple5>

; <Start encoding assume FStar.Pervasives.Native.tuple5__uu___haseq>
; </end encoding assume FStar.Pervasives.Native.tuple5__uu___haseq>

; <Start encoding val FStar.Pervasives.Native.uu___is_Mktuple5>
(declare-fun FStar.Pervasives.Native.uu___is_Mktuple5 (Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_cfa2e2c8b8b41312889ff659c4faa5f9 () Term)
(declare-fun FStar.Pervasives.Native.uu___is_Mktuple5@tok () Term)
; </end encoding val FStar.Pervasives.Native.uu___is_Mktuple5>

; <Skipped let uu___is_Mktuple5/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple5__item___1>
(declare-fun FStar.Pervasives.Native.__proj__Mktuple5__item___1 (Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_7519f72fe101267af170e00c6ce694af () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple5__item___1@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple5__item___1>

; <Skipped let __proj__Mktuple5__item___1/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple5__item___2>
(declare-fun FStar.Pervasives.Native.__proj__Mktuple5__item___2 (Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_3e46329f224aa70981a337f98afbaa87 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple5__item___2@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple5__item___2>

; <Skipped let __proj__Mktuple5__item___2/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple5__item___3>
(declare-fun FStar.Pervasives.Native.__proj__Mktuple5__item___3 (Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_55e6dc1b736536de45fedf844003f847 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple5__item___3@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple5__item___3>

; <Skipped let __proj__Mktuple5__item___3/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple5__item___4>
(declare-fun FStar.Pervasives.Native.__proj__Mktuple5__item___4 (Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_3a4e86c6aee1a39b4811bdbc12405398 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple5__item___4@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple5__item___4>

; <Skipped let __proj__Mktuple5__item___4/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple5__item___5>
(declare-fun FStar.Pervasives.Native.__proj__Mktuple5__item___5 (Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_1a78355922fdaba3f3848932dfc0a089 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple5__item___5@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple5__item___5>

; <Skipped let __proj__Mktuple5__item___5/>

; <Start encoding type FStar.Pervasives.Native.tuple6>
; Constructor
(declare-fun FStar.Pervasives.Native.tuple6 (Term Term Term Term Term Term) Term)
; token
(declare-fun FStar.Pervasives.Native.tuple6@tok () Term)
; Constructor
(declare-fun
 FStar.Pervasives.Native.Mktuple6
 (Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple6__a (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple6__b (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple6__c (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple6__d (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple6__e (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple6__f (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple6__1 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple6__2 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple6__3 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple6__4 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple6__5 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple6__6 (Term) Term)
; data constructor proxy: FStar.Pervasives.Native.Mktuple6
(declare-fun FStar.Pervasives.Native.Mktuple6@tok () Term)
(declare-fun Tm_arrow_f277ffaa7e891207f9c6bff5b88ffd67 () Term)
; <start constructor FStar.Pervasives.Native.tuple6>
; Discriminator definition
(define-fun is-FStar.Pervasives.Native.tuple6 ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 209)
  (exists ((@x0 Term) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term) (@x5 Term))
   (! (= __@x0 (FStar.Pervasives.Native.tuple6 @x0 @x1 @x2 @x3 @x4 @x5))
    :qid is-FStar.Pervasives.Native.tuple6))))
; </end constructor FStar.Pervasives.Native.tuple6>
; <start constructor FStar.Pervasives.Native.Mktuple6>
; Discriminator definition
(define-fun is-FStar.Pervasives.Native.Mktuple6 ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 216)
  (=
   __@x0
   (FStar.Pervasives.Native.Mktuple6
    (FStar.Pervasives.Native.Mktuple6__a __@x0)
    (FStar.Pervasives.Native.Mktuple6__b __@x0)
    (FStar.Pervasives.Native.Mktuple6__c __@x0)
    (FStar.Pervasives.Native.Mktuple6__d __@x0)
    (FStar.Pervasives.Native.Mktuple6__e __@x0)
    (FStar.Pervasives.Native.Mktuple6__f __@x0)
    (FStar.Pervasives.Native.Mktuple6__1 __@x0)
    (FStar.Pervasives.Native.Mktuple6__2 __@x0)
    (FStar.Pervasives.Native.Mktuple6__3 __@x0)
    (FStar.Pervasives.Native.Mktuple6__4 __@x0)
    (FStar.Pervasives.Native.Mktuple6__5 __@x0)
    (FStar.Pervasives.Native.Mktuple6__6 __@x0)))))
; </end constructor FStar.Pervasives.Native.Mktuple6>
; </end encoding type FStar.Pervasives.Native.tuple6>

; <Start encoding assume FStar.Pervasives.Native.tuple6__uu___haseq>
; </end encoding assume FStar.Pervasives.Native.tuple6__uu___haseq>

; <Start encoding val FStar.Pervasives.Native.uu___is_Mktuple6>
(declare-fun FStar.Pervasives.Native.uu___is_Mktuple6 (Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_286587a1b9d299ba75a076f54a6dad5f () Term)
(declare-fun FStar.Pervasives.Native.uu___is_Mktuple6@tok () Term)
; </end encoding val FStar.Pervasives.Native.uu___is_Mktuple6>

; <Skipped let uu___is_Mktuple6/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple6__item___1>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple6__item___1
 (Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_5b1e145eeceab869b8e427e6927dbd63 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple6__item___1@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple6__item___1>

; <Skipped let __proj__Mktuple6__item___1/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple6__item___2>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple6__item___2
 (Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_3207475e225d584881d3e0a297482887 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple6__item___2@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple6__item___2>

; <Skipped let __proj__Mktuple6__item___2/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple6__item___3>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple6__item___3
 (Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_43e491b3b537a523a4f10de18b1915f5 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple6__item___3@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple6__item___3>

; <Skipped let __proj__Mktuple6__item___3/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple6__item___4>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple6__item___4
 (Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_f5747d5b721642d7ecb757b043f20880 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple6__item___4@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple6__item___4>

; <Skipped let __proj__Mktuple6__item___4/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple6__item___5>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple6__item___5
 (Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_d6501381a0206e157ecc43950bb31fea () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple6__item___5@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple6__item___5>

; <Skipped let __proj__Mktuple6__item___5/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple6__item___6>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple6__item___6
 (Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_9c342f41120d0c7aea115b09b58cefb2 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple6__item___6@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple6__item___6>

; <Skipped let __proj__Mktuple6__item___6/>

; <Start encoding type FStar.Pervasives.Native.tuple7>
; Constructor
(declare-fun FStar.Pervasives.Native.tuple7 (Term Term Term Term Term Term Term) Term)
; token
(declare-fun FStar.Pervasives.Native.tuple7@tok () Term)
; Constructor
(declare-fun
 FStar.Pervasives.Native.Mktuple7
 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple7__a (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple7__b (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple7__c (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple7__d (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple7__e (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple7__f (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple7__g (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple7__1 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple7__2 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple7__3 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple7__4 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple7__5 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple7__6 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple7__7 (Term) Term)
; data constructor proxy: FStar.Pervasives.Native.Mktuple7
(declare-fun FStar.Pervasives.Native.Mktuple7@tok () Term)
(declare-fun Tm_arrow_37ee9ec407a0f7bb69bf1b308f74a230 () Term)
; <start constructor FStar.Pervasives.Native.tuple7>
; Discriminator definition
(define-fun is-FStar.Pervasives.Native.tuple7 ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 234)
  (exists ((@x0 Term) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term) (@x5 Term) (@x6 Term))
   (! (= __@x0 (FStar.Pervasives.Native.tuple7 @x0 @x1 @x2 @x3 @x4 @x5 @x6))
    :qid is-FStar.Pervasives.Native.tuple7))))
; </end constructor FStar.Pervasives.Native.tuple7>
; <start constructor FStar.Pervasives.Native.Mktuple7>
; Discriminator definition
(define-fun is-FStar.Pervasives.Native.Mktuple7 ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 241)
  (=
   __@x0
   (FStar.Pervasives.Native.Mktuple7
    (FStar.Pervasives.Native.Mktuple7__a __@x0)
    (FStar.Pervasives.Native.Mktuple7__b __@x0)
    (FStar.Pervasives.Native.Mktuple7__c __@x0)
    (FStar.Pervasives.Native.Mktuple7__d __@x0)
    (FStar.Pervasives.Native.Mktuple7__e __@x0)
    (FStar.Pervasives.Native.Mktuple7__f __@x0)
    (FStar.Pervasives.Native.Mktuple7__g __@x0)
    (FStar.Pervasives.Native.Mktuple7__1 __@x0)
    (FStar.Pervasives.Native.Mktuple7__2 __@x0)
    (FStar.Pervasives.Native.Mktuple7__3 __@x0)
    (FStar.Pervasives.Native.Mktuple7__4 __@x0)
    (FStar.Pervasives.Native.Mktuple7__5 __@x0)
    (FStar.Pervasives.Native.Mktuple7__6 __@x0)
    (FStar.Pervasives.Native.Mktuple7__7 __@x0)))))
; </end constructor FStar.Pervasives.Native.Mktuple7>
; </end encoding type FStar.Pervasives.Native.tuple7>

; <Start encoding assume FStar.Pervasives.Native.tuple7__uu___haseq>
; </end encoding assume FStar.Pervasives.Native.tuple7__uu___haseq>

; <Start encoding val FStar.Pervasives.Native.uu___is_Mktuple7>
(declare-fun FStar.Pervasives.Native.uu___is_Mktuple7 (Term Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_612dde2fedb1440c5d790ba7f5015319 () Term)
(declare-fun FStar.Pervasives.Native.uu___is_Mktuple7@tok () Term)
; </end encoding val FStar.Pervasives.Native.uu___is_Mktuple7>

; <Skipped let uu___is_Mktuple7/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple7__item___1>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple7__item___1
 (Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_01c4488a68699f466c59799f5c1173ff () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple7__item___1@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple7__item___1>

; <Skipped let __proj__Mktuple7__item___1/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple7__item___2>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple7__item___2
 (Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_f317591858699585c67fe4ba8664e34c () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple7__item___2@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple7__item___2>

; <Skipped let __proj__Mktuple7__item___2/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple7__item___3>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple7__item___3
 (Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_44afce9d86f095aacc82b3ea2e0e223c () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple7__item___3@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple7__item___3>

; <Skipped let __proj__Mktuple7__item___3/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple7__item___4>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple7__item___4
 (Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_e857539d4cc5be0510cbcfb97cb64b35 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple7__item___4@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple7__item___4>

; <Skipped let __proj__Mktuple7__item___4/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple7__item___5>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple7__item___5
 (Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_a249d3d5ba06026b12d41e289bb88061 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple7__item___5@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple7__item___5>

; <Skipped let __proj__Mktuple7__item___5/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple7__item___6>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple7__item___6
 (Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_bf614c740d11cac9b5f8eb20b24c7d00 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple7__item___6@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple7__item___6>

; <Skipped let __proj__Mktuple7__item___6/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple7__item___7>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple7__item___7
 (Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_e775fbf03b08091e48143165286522f7 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple7__item___7@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple7__item___7>

; <Skipped let __proj__Mktuple7__item___7/>

; <Start encoding type FStar.Pervasives.Native.tuple8>
; Constructor
(declare-fun FStar.Pervasives.Native.tuple8 (Term Term Term Term Term Term Term Term) Term)
; token
(declare-fun FStar.Pervasives.Native.tuple8@tok () Term)
; Constructor
(declare-fun
 FStar.Pervasives.Native.Mktuple8
 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple8__a (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple8__b (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple8__c (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple8__d (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple8__e (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple8__f (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple8__g (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple8__h (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple8__1 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple8__2 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple8__3 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple8__4 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple8__5 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple8__6 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple8__7 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple8__8 (Term) Term)
; data constructor proxy: FStar.Pervasives.Native.Mktuple8
(declare-fun FStar.Pervasives.Native.Mktuple8@tok () Term)
(declare-fun Tm_arrow_e922a339a0aa0f375ed7113049811583 () Term)
; <start constructor FStar.Pervasives.Native.tuple8>
; Discriminator definition
(define-fun is-FStar.Pervasives.Native.tuple8 ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 261)
  (exists ((@x0 Term) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term) (@x5 Term) (@x6 Term) (@x7 Term))
   (! (= __@x0 (FStar.Pervasives.Native.tuple8 @x0 @x1 @x2 @x3 @x4 @x5 @x6 @x7))
    :qid is-FStar.Pervasives.Native.tuple8))))
; </end constructor FStar.Pervasives.Native.tuple8>
; <start constructor FStar.Pervasives.Native.Mktuple8>
; Discriminator definition
(define-fun is-FStar.Pervasives.Native.Mktuple8 ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 268)
  (=
   __@x0
   (FStar.Pervasives.Native.Mktuple8
    (FStar.Pervasives.Native.Mktuple8__a __@x0)
    (FStar.Pervasives.Native.Mktuple8__b __@x0)
    (FStar.Pervasives.Native.Mktuple8__c __@x0)
    (FStar.Pervasives.Native.Mktuple8__d __@x0)
    (FStar.Pervasives.Native.Mktuple8__e __@x0)
    (FStar.Pervasives.Native.Mktuple8__f __@x0)
    (FStar.Pervasives.Native.Mktuple8__g __@x0)
    (FStar.Pervasives.Native.Mktuple8__h __@x0)
    (FStar.Pervasives.Native.Mktuple8__1 __@x0)
    (FStar.Pervasives.Native.Mktuple8__2 __@x0)
    (FStar.Pervasives.Native.Mktuple8__3 __@x0)
    (FStar.Pervasives.Native.Mktuple8__4 __@x0)
    (FStar.Pervasives.Native.Mktuple8__5 __@x0)
    (FStar.Pervasives.Native.Mktuple8__6 __@x0)
    (FStar.Pervasives.Native.Mktuple8__7 __@x0)
    (FStar.Pervasives.Native.Mktuple8__8 __@x0)))))
; </end constructor FStar.Pervasives.Native.Mktuple8>
; </end encoding type FStar.Pervasives.Native.tuple8>

; <Start encoding assume FStar.Pervasives.Native.tuple8__uu___haseq>
; </end encoding assume FStar.Pervasives.Native.tuple8__uu___haseq>

; <Start encoding val FStar.Pervasives.Native.uu___is_Mktuple8>
(declare-fun
 FStar.Pervasives.Native.uu___is_Mktuple8
 (Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_ee31533e24c78558f4566668a6ec027c () Term)
(declare-fun FStar.Pervasives.Native.uu___is_Mktuple8@tok () Term)
; </end encoding val FStar.Pervasives.Native.uu___is_Mktuple8>

; <Skipped let uu___is_Mktuple8/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple8__item___1>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple8__item___1
 (Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_c971649e117e4941e7317eff508d5ea7 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple8__item___1@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple8__item___1>

; <Skipped let __proj__Mktuple8__item___1/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple8__item___2>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple8__item___2
 (Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_97dd51e3888c1c543d8f6c73d1808548 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple8__item___2@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple8__item___2>

; <Skipped let __proj__Mktuple8__item___2/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple8__item___3>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple8__item___3
 (Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_3931d1873633dc65fed4e022ee3df3ca () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple8__item___3@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple8__item___3>

; <Skipped let __proj__Mktuple8__item___3/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple8__item___4>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple8__item___4
 (Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_5c791e62f9472e4c351c2befb2b7a3d8 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple8__item___4@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple8__item___4>

; <Skipped let __proj__Mktuple8__item___4/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple8__item___5>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple8__item___5
 (Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_7ef7cac898ca0ef25893959e91d8c6ce () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple8__item___5@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple8__item___5>

; <Skipped let __proj__Mktuple8__item___5/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple8__item___6>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple8__item___6
 (Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_b0ae5f58a7fa002e0313b58bf5fc74cb () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple8__item___6@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple8__item___6>

; <Skipped let __proj__Mktuple8__item___6/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple8__item___7>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple8__item___7
 (Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_7fcd94f7549ca8acfadc26bc5b82f590 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple8__item___7@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple8__item___7>

; <Skipped let __proj__Mktuple8__item___7/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple8__item___8>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple8__item___8
 (Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_feaaf61fa62fef18c5ee7c39e9f86573 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple8__item___8@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple8__item___8>

; <Skipped let __proj__Mktuple8__item___8/>

; <Start encoding type FStar.Pervasives.Native.tuple9>
; Constructor
(declare-fun FStar.Pervasives.Native.tuple9 (Term Term Term Term Term Term Term Term Term) Term)
; token
(declare-fun FStar.Pervasives.Native.tuple9@tok () Term)
; Constructor
(declare-fun
 FStar.Pervasives.Native.Mktuple9
 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple9__a (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple9__b (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple9__c (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple9__d (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple9__e (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple9__f (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple9__g (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple9__h (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple9__i (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple9__1 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple9__2 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple9__3 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple9__4 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple9__5 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple9__6 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple9__7 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple9__8 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple9__9 (Term) Term)
; data constructor proxy: FStar.Pervasives.Native.Mktuple9
(declare-fun FStar.Pervasives.Native.Mktuple9@tok () Term)
(declare-fun Tm_arrow_0c6bc368a301d7de6e1939ebea91ee60 () Term)
; <start constructor FStar.Pervasives.Native.tuple9>
; Discriminator definition
(define-fun is-FStar.Pervasives.Native.tuple9 ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 290)
  (exists
    ((@x0 Term)
     (@x1 Term)
     (@x2 Term)
     (@x3 Term)
     (@x4 Term)
     (@x5 Term)
     (@x6 Term)
     (@x7 Term)
     (@x8 Term))
   (! (= __@x0 (FStar.Pervasives.Native.tuple9 @x0 @x1 @x2 @x3 @x4 @x5 @x6 @x7 @x8))
    :qid is-FStar.Pervasives.Native.tuple9))))
; </end constructor FStar.Pervasives.Native.tuple9>
; <start constructor FStar.Pervasives.Native.Mktuple9>
; Discriminator definition
(define-fun is-FStar.Pervasives.Native.Mktuple9 ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 297)
  (=
   __@x0
   (FStar.Pervasives.Native.Mktuple9
    (FStar.Pervasives.Native.Mktuple9__a __@x0)
    (FStar.Pervasives.Native.Mktuple9__b __@x0)
    (FStar.Pervasives.Native.Mktuple9__c __@x0)
    (FStar.Pervasives.Native.Mktuple9__d __@x0)
    (FStar.Pervasives.Native.Mktuple9__e __@x0)
    (FStar.Pervasives.Native.Mktuple9__f __@x0)
    (FStar.Pervasives.Native.Mktuple9__g __@x0)
    (FStar.Pervasives.Native.Mktuple9__h __@x0)
    (FStar.Pervasives.Native.Mktuple9__i __@x0)
    (FStar.Pervasives.Native.Mktuple9__1 __@x0)
    (FStar.Pervasives.Native.Mktuple9__2 __@x0)
    (FStar.Pervasives.Native.Mktuple9__3 __@x0)
    (FStar.Pervasives.Native.Mktuple9__4 __@x0)
    (FStar.Pervasives.Native.Mktuple9__5 __@x0)
    (FStar.Pervasives.Native.Mktuple9__6 __@x0)
    (FStar.Pervasives.Native.Mktuple9__7 __@x0)
    (FStar.Pervasives.Native.Mktuple9__8 __@x0)
    (FStar.Pervasives.Native.Mktuple9__9 __@x0)))))
; </end constructor FStar.Pervasives.Native.Mktuple9>
; </end encoding type FStar.Pervasives.Native.tuple9>

; <Start encoding assume FStar.Pervasives.Native.tuple9__uu___haseq>
; </end encoding assume FStar.Pervasives.Native.tuple9__uu___haseq>

; <Start encoding val FStar.Pervasives.Native.uu___is_Mktuple9>
(declare-fun
 FStar.Pervasives.Native.uu___is_Mktuple9
 (Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_9ac8f39c7b1df1e87db7c9bf5bc37a38 () Term)
(declare-fun FStar.Pervasives.Native.uu___is_Mktuple9@tok () Term)
; </end encoding val FStar.Pervasives.Native.uu___is_Mktuple9>

; <Skipped let uu___is_Mktuple9/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple9__item___1>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple9__item___1
 (Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_270119cc1f13c9afeb25322d78efc328 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple9__item___1@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple9__item___1>

; <Skipped let __proj__Mktuple9__item___1/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple9__item___2>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple9__item___2
 (Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_3c368dee2c86a1af7bd7ea91baab7613 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple9__item___2@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple9__item___2>

; <Skipped let __proj__Mktuple9__item___2/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple9__item___3>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple9__item___3
 (Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_e9c745e2da3dec50930b0a7e01a11cc3 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple9__item___3@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple9__item___3>

; <Skipped let __proj__Mktuple9__item___3/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple9__item___4>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple9__item___4
 (Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_a82ff41c5c66cd37481c83584c94a54d () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple9__item___4@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple9__item___4>

; <Skipped let __proj__Mktuple9__item___4/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple9__item___5>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple9__item___5
 (Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_1b3b4c5e68fdf7277f64bde93e6534de () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple9__item___5@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple9__item___5>

; <Skipped let __proj__Mktuple9__item___5/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple9__item___6>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple9__item___6
 (Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_837f1324f6fa51bb8a0e45ee48e4e058 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple9__item___6@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple9__item___6>

; <Skipped let __proj__Mktuple9__item___6/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple9__item___7>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple9__item___7
 (Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_a7562220963e3431d35de76c3c9c87b9 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple9__item___7@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple9__item___7>

; <Skipped let __proj__Mktuple9__item___7/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple9__item___8>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple9__item___8
 (Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_861b810bc1c20bbd221cecbce824b695 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple9__item___8@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple9__item___8>

; <Skipped let __proj__Mktuple9__item___8/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple9__item___9>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple9__item___9
 (Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_9a54b18d8e08fdf0e20244b3f960c9dc () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple9__item___9@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple9__item___9>

; <Skipped let __proj__Mktuple9__item___9/>

; <Start encoding type FStar.Pervasives.Native.tuple10>
; Constructor
(declare-fun
 FStar.Pervasives.Native.tuple10
 (Term Term Term Term Term Term Term Term Term Term)
 Term)
; token
(declare-fun FStar.Pervasives.Native.tuple10@tok () Term)
; Constructor
(declare-fun
 FStar.Pervasives.Native.Mktuple10
 (Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term)
 Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple10__a (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple10__b (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple10__c (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple10__d (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple10__e (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple10__f (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple10__g (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple10__h (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple10__i (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple10__j (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple10__1 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple10__2 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple10__3 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple10__4 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple10__5 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple10__6 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple10__7 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple10__8 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple10__9 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple10__10 (Term) Term)
; data constructor proxy: FStar.Pervasives.Native.Mktuple10
(declare-fun FStar.Pervasives.Native.Mktuple10@tok () Term)
(declare-fun Tm_arrow_61d31241317018093b2245d256adbcb5 () Term)
; <start constructor FStar.Pervasives.Native.tuple10>
; Discriminator definition
(define-fun is-FStar.Pervasives.Native.tuple10 ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 321)
  (exists
    ((@x0 Term)
     (@x1 Term)
     (@x2 Term)
     (@x3 Term)
     (@x4 Term)
     (@x5 Term)
     (@x6 Term)
     (@x7 Term)
     (@x8 Term)
     (@x9 Term))
   (! (= __@x0 (FStar.Pervasives.Native.tuple10 @x0 @x1 @x2 @x3 @x4 @x5 @x6 @x7 @x8 @x9))
    :qid is-FStar.Pervasives.Native.tuple10))))
; </end constructor FStar.Pervasives.Native.tuple10>
; <start constructor FStar.Pervasives.Native.Mktuple10>
; Discriminator definition
(define-fun is-FStar.Pervasives.Native.Mktuple10 ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 328)
  (=
   __@x0
   (FStar.Pervasives.Native.Mktuple10
    (FStar.Pervasives.Native.Mktuple10__a __@x0)
    (FStar.Pervasives.Native.Mktuple10__b __@x0)
    (FStar.Pervasives.Native.Mktuple10__c __@x0)
    (FStar.Pervasives.Native.Mktuple10__d __@x0)
    (FStar.Pervasives.Native.Mktuple10__e __@x0)
    (FStar.Pervasives.Native.Mktuple10__f __@x0)
    (FStar.Pervasives.Native.Mktuple10__g __@x0)
    (FStar.Pervasives.Native.Mktuple10__h __@x0)
    (FStar.Pervasives.Native.Mktuple10__i __@x0)
    (FStar.Pervasives.Native.Mktuple10__j __@x0)
    (FStar.Pervasives.Native.Mktuple10__1 __@x0)
    (FStar.Pervasives.Native.Mktuple10__2 __@x0)
    (FStar.Pervasives.Native.Mktuple10__3 __@x0)
    (FStar.Pervasives.Native.Mktuple10__4 __@x0)
    (FStar.Pervasives.Native.Mktuple10__5 __@x0)
    (FStar.Pervasives.Native.Mktuple10__6 __@x0)
    (FStar.Pervasives.Native.Mktuple10__7 __@x0)
    (FStar.Pervasives.Native.Mktuple10__8 __@x0)
    (FStar.Pervasives.Native.Mktuple10__9 __@x0)
    (FStar.Pervasives.Native.Mktuple10__10 __@x0)))))
; </end constructor FStar.Pervasives.Native.Mktuple10>
; </end encoding type FStar.Pervasives.Native.tuple10>

; <Start encoding assume FStar.Pervasives.Native.tuple10__uu___haseq>
; </end encoding assume FStar.Pervasives.Native.tuple10__uu___haseq>

; <Start encoding val FStar.Pervasives.Native.uu___is_Mktuple10>
(declare-fun
 FStar.Pervasives.Native.uu___is_Mktuple10
 (Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_f27282a056f525d8710bf32204d252ec () Term)
(declare-fun FStar.Pervasives.Native.uu___is_Mktuple10@tok () Term)
; </end encoding val FStar.Pervasives.Native.uu___is_Mktuple10>

; <Skipped let uu___is_Mktuple10/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple10__item___1>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple10__item___1
 (Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_c581e9177cd071a1b6e057fca49ea75b () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple10__item___1@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple10__item___1>

; <Skipped let __proj__Mktuple10__item___1/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple10__item___2>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple10__item___2
 (Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_ae4b2db87d7c69a8380f4d5ae20f2149 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple10__item___2@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple10__item___2>

; <Skipped let __proj__Mktuple10__item___2/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple10__item___3>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple10__item___3
 (Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_a21274cb112dc6619b2bde244e6a0f9a () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple10__item___3@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple10__item___3>

; <Skipped let __proj__Mktuple10__item___3/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple10__item___4>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple10__item___4
 (Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_9a051d5cacf4367d170d590ba8bb720d () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple10__item___4@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple10__item___4>

; <Skipped let __proj__Mktuple10__item___4/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple10__item___5>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple10__item___5
 (Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_bbd73769b626202d4de52d4d60cd3b75 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple10__item___5@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple10__item___5>

; <Skipped let __proj__Mktuple10__item___5/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple10__item___6>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple10__item___6
 (Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_7ceeded5a3852448c1a5406becbd990e () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple10__item___6@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple10__item___6>

; <Skipped let __proj__Mktuple10__item___6/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple10__item___7>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple10__item___7
 (Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_c68947c71d484ad43cd50646c4e1daf4 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple10__item___7@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple10__item___7>

; <Skipped let __proj__Mktuple10__item___7/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple10__item___8>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple10__item___8
 (Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_e7b9ff90289491020fe84c6ab3bc60c6 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple10__item___8@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple10__item___8>

; <Skipped let __proj__Mktuple10__item___8/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple10__item___9>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple10__item___9
 (Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_6dbb3170f112f78092d1caee0b341678 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple10__item___9@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple10__item___9>

; <Skipped let __proj__Mktuple10__item___9/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple10__item___10>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple10__item___10
 (Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_45598a99c0a7fcc1bf2258b9ad4256cf () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple10__item___10@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple10__item___10>

; <Skipped let __proj__Mktuple10__item___10/>

; <Start encoding type FStar.Pervasives.Native.tuple11>
; Constructor
(declare-fun
 FStar.Pervasives.Native.tuple11
 (Term Term Term Term Term Term Term Term Term Term Term)
 Term)
; token
(declare-fun FStar.Pervasives.Native.tuple11@tok () Term)
; Constructor
(declare-fun
 FStar.Pervasives.Native.Mktuple11
 (Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term)
 Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple11__a (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple11__b (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple11__c (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple11__d (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple11__e (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple11__f (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple11__g (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple11__h (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple11__i (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple11__j (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple11__k (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple11__1 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple11__2 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple11__3 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple11__4 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple11__5 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple11__6 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple11__7 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple11__8 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple11__9 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple11__10 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple11__11 (Term) Term)
; data constructor proxy: FStar.Pervasives.Native.Mktuple11
(declare-fun FStar.Pervasives.Native.Mktuple11@tok () Term)
(declare-fun Tm_arrow_bf9783a1a3bf19ab918f42acff1daa32 () Term)
; <start constructor FStar.Pervasives.Native.tuple11>
; Discriminator definition
(define-fun is-FStar.Pervasives.Native.tuple11 ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 354)
  (exists
    ((@x0 Term)
     (@x1 Term)
     (@x2 Term)
     (@x3 Term)
     (@x4 Term)
     (@x5 Term)
     (@x6 Term)
     (@x7 Term)
     (@x8 Term)
     (@x9 Term)
     (@x10 Term))
   (! (= __@x0 (FStar.Pervasives.Native.tuple11 @x0 @x1 @x2 @x3 @x4 @x5 @x6 @x7 @x8 @x9 @x10))
    :qid is-FStar.Pervasives.Native.tuple11))))
; </end constructor FStar.Pervasives.Native.tuple11>
; <start constructor FStar.Pervasives.Native.Mktuple11>
; Discriminator definition
(define-fun is-FStar.Pervasives.Native.Mktuple11 ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 361)
  (=
   __@x0
   (FStar.Pervasives.Native.Mktuple11
    (FStar.Pervasives.Native.Mktuple11__a __@x0)
    (FStar.Pervasives.Native.Mktuple11__b __@x0)
    (FStar.Pervasives.Native.Mktuple11__c __@x0)
    (FStar.Pervasives.Native.Mktuple11__d __@x0)
    (FStar.Pervasives.Native.Mktuple11__e __@x0)
    (FStar.Pervasives.Native.Mktuple11__f __@x0)
    (FStar.Pervasives.Native.Mktuple11__g __@x0)
    (FStar.Pervasives.Native.Mktuple11__h __@x0)
    (FStar.Pervasives.Native.Mktuple11__i __@x0)
    (FStar.Pervasives.Native.Mktuple11__j __@x0)
    (FStar.Pervasives.Native.Mktuple11__k __@x0)
    (FStar.Pervasives.Native.Mktuple11__1 __@x0)
    (FStar.Pervasives.Native.Mktuple11__2 __@x0)
    (FStar.Pervasives.Native.Mktuple11__3 __@x0)
    (FStar.Pervasives.Native.Mktuple11__4 __@x0)
    (FStar.Pervasives.Native.Mktuple11__5 __@x0)
    (FStar.Pervasives.Native.Mktuple11__6 __@x0)
    (FStar.Pervasives.Native.Mktuple11__7 __@x0)
    (FStar.Pervasives.Native.Mktuple11__8 __@x0)
    (FStar.Pervasives.Native.Mktuple11__9 __@x0)
    (FStar.Pervasives.Native.Mktuple11__10 __@x0)
    (FStar.Pervasives.Native.Mktuple11__11 __@x0)))))
; </end constructor FStar.Pervasives.Native.Mktuple11>
; </end encoding type FStar.Pervasives.Native.tuple11>

; <Start encoding assume FStar.Pervasives.Native.tuple11__uu___haseq>
; </end encoding assume FStar.Pervasives.Native.tuple11__uu___haseq>

; <Start encoding val FStar.Pervasives.Native.uu___is_Mktuple11>
(declare-fun
 FStar.Pervasives.Native.uu___is_Mktuple11
 (Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_005819ee7a23a5c47189bae72b85d85c () Term)
(declare-fun FStar.Pervasives.Native.uu___is_Mktuple11@tok () Term)
; </end encoding val FStar.Pervasives.Native.uu___is_Mktuple11>

; <Skipped let uu___is_Mktuple11/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple11__item___1>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple11__item___1
 (Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_31968e334e9582d95281307f534992a9 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple11__item___1@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple11__item___1>

; <Skipped let __proj__Mktuple11__item___1/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple11__item___2>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple11__item___2
 (Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_6252dd9f4473dc54a3482810e8556404 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple11__item___2@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple11__item___2>

; <Skipped let __proj__Mktuple11__item___2/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple11__item___3>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple11__item___3
 (Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_ec3ce6b7406c091cd7d0961922bb5a02 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple11__item___3@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple11__item___3>

; <Skipped let __proj__Mktuple11__item___3/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple11__item___4>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple11__item___4
 (Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_be7571e73b0e7fc24d03efe0e003c054 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple11__item___4@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple11__item___4>

; <Skipped let __proj__Mktuple11__item___4/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple11__item___5>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple11__item___5
 (Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_97ae7d913e508c46c48c3b51553d4459 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple11__item___5@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple11__item___5>

; <Skipped let __proj__Mktuple11__item___5/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple11__item___6>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple11__item___6
 (Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_1dca311798936510e0ead61e14cf32a6 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple11__item___6@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple11__item___6>

; <Skipped let __proj__Mktuple11__item___6/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple11__item___7>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple11__item___7
 (Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_eec431ea31093a646681ef2ceb2e2986 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple11__item___7@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple11__item___7>

; <Skipped let __proj__Mktuple11__item___7/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple11__item___8>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple11__item___8
 (Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_689b2f06e9fd83f7a84ce80a13d338c6 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple11__item___8@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple11__item___8>

; <Skipped let __proj__Mktuple11__item___8/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple11__item___9>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple11__item___9
 (Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_20210a3d9498f929cb7aa68d9e8b5ebf () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple11__item___9@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple11__item___9>

; <Skipped let __proj__Mktuple11__item___9/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple11__item___10>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple11__item___10
 (Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_96812f2124d88760b2002bbe1502c3c9 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple11__item___10@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple11__item___10>

; <Skipped let __proj__Mktuple11__item___10/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple11__item___11>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple11__item___11
 (Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_abcfa2582f68905d460c5ef4a7642f2d () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple11__item___11@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple11__item___11>

; <Skipped let __proj__Mktuple11__item___11/>

; <Start encoding type FStar.Pervasives.Native.tuple12>
; Constructor
(declare-fun
 FStar.Pervasives.Native.tuple12
 (Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
; token
(declare-fun FStar.Pervasives.Native.tuple12@tok () Term)
; Constructor
(declare-fun
 FStar.Pervasives.Native.Mktuple12
 (Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term)
 Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple12__a (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple12__b (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple12__c (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple12__d (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple12__e (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple12__f (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple12__g (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple12__h (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple12__i (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple12__j (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple12__k (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple12__l (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple12__1 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple12__2 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple12__3 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple12__4 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple12__5 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple12__6 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple12__7 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple12__8 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple12__9 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple12__10 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple12__11 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple12__12 (Term) Term)
; data constructor proxy: FStar.Pervasives.Native.Mktuple12
(declare-fun FStar.Pervasives.Native.Mktuple12@tok () Term)
(declare-fun Tm_arrow_4d5cd995d6f44a2ec39d0f193be0be65 () Term)
; <start constructor FStar.Pervasives.Native.tuple12>
; Discriminator definition
(define-fun is-FStar.Pervasives.Native.tuple12 ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 389)
  (exists
    ((@x0 Term)
     (@x1 Term)
     (@x2 Term)
     (@x3 Term)
     (@x4 Term)
     (@x5 Term)
     (@x6 Term)
     (@x7 Term)
     (@x8 Term)
     (@x9 Term)
     (@x10 Term)
     (@x11 Term))
   (! (= __@x0 (FStar.Pervasives.Native.tuple12 @x0 @x1 @x2 @x3 @x4 @x5 @x6 @x7 @x8 @x9 @x10 @x11))
    :qid is-FStar.Pervasives.Native.tuple12))))
; </end constructor FStar.Pervasives.Native.tuple12>
; <start constructor FStar.Pervasives.Native.Mktuple12>
; Discriminator definition
(define-fun is-FStar.Pervasives.Native.Mktuple12 ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 396)
  (=
   __@x0
   (FStar.Pervasives.Native.Mktuple12
    (FStar.Pervasives.Native.Mktuple12__a __@x0)
    (FStar.Pervasives.Native.Mktuple12__b __@x0)
    (FStar.Pervasives.Native.Mktuple12__c __@x0)
    (FStar.Pervasives.Native.Mktuple12__d __@x0)
    (FStar.Pervasives.Native.Mktuple12__e __@x0)
    (FStar.Pervasives.Native.Mktuple12__f __@x0)
    (FStar.Pervasives.Native.Mktuple12__g __@x0)
    (FStar.Pervasives.Native.Mktuple12__h __@x0)
    (FStar.Pervasives.Native.Mktuple12__i __@x0)
    (FStar.Pervasives.Native.Mktuple12__j __@x0)
    (FStar.Pervasives.Native.Mktuple12__k __@x0)
    (FStar.Pervasives.Native.Mktuple12__l __@x0)
    (FStar.Pervasives.Native.Mktuple12__1 __@x0)
    (FStar.Pervasives.Native.Mktuple12__2 __@x0)
    (FStar.Pervasives.Native.Mktuple12__3 __@x0)
    (FStar.Pervasives.Native.Mktuple12__4 __@x0)
    (FStar.Pervasives.Native.Mktuple12__5 __@x0)
    (FStar.Pervasives.Native.Mktuple12__6 __@x0)
    (FStar.Pervasives.Native.Mktuple12__7 __@x0)
    (FStar.Pervasives.Native.Mktuple12__8 __@x0)
    (FStar.Pervasives.Native.Mktuple12__9 __@x0)
    (FStar.Pervasives.Native.Mktuple12__10 __@x0)
    (FStar.Pervasives.Native.Mktuple12__11 __@x0)
    (FStar.Pervasives.Native.Mktuple12__12 __@x0)))))
; </end constructor FStar.Pervasives.Native.Mktuple12>
; </end encoding type FStar.Pervasives.Native.tuple12>

; <Start encoding assume FStar.Pervasives.Native.tuple12__uu___haseq>
; </end encoding assume FStar.Pervasives.Native.tuple12__uu___haseq>

; <Start encoding val FStar.Pervasives.Native.uu___is_Mktuple12>
(declare-fun
 FStar.Pervasives.Native.uu___is_Mktuple12
 (Term Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_5c9f47d9090f554c9826d2f65e388f20 () Term)
(declare-fun FStar.Pervasives.Native.uu___is_Mktuple12@tok () Term)
; </end encoding val FStar.Pervasives.Native.uu___is_Mktuple12>

; <Skipped let uu___is_Mktuple12/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple12__item___1>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple12__item___1
 (Term Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_618941d7cf5ddbaabe15df8579b4a387 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple12__item___1@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple12__item___1>

; <Skipped let __proj__Mktuple12__item___1/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple12__item___2>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple12__item___2
 (Term Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_84e9e2280e9bcb3233e4f33f86d66ea6 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple12__item___2@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple12__item___2>

; <Skipped let __proj__Mktuple12__item___2/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple12__item___3>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple12__item___3
 (Term Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_1fa79c5abf9f18607bd2e46a1a6967fa () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple12__item___3@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple12__item___3>

; <Skipped let __proj__Mktuple12__item___3/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple12__item___4>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple12__item___4
 (Term Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_0f49c582489d782b08195e81221181dc () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple12__item___4@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple12__item___4>

; <Skipped let __proj__Mktuple12__item___4/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple12__item___5>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple12__item___5
 (Term Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_29b7181ebb44f9e4a45f95c4f8478c6a () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple12__item___5@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple12__item___5>

; <Skipped let __proj__Mktuple12__item___5/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple12__item___6>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple12__item___6
 (Term Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_3cc2863a7d7f23e3916fa1e43483cb90 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple12__item___6@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple12__item___6>

; <Skipped let __proj__Mktuple12__item___6/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple12__item___7>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple12__item___7
 (Term Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_c7deea49701ab64a73985bf522e46359 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple12__item___7@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple12__item___7>

; <Skipped let __proj__Mktuple12__item___7/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple12__item___8>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple12__item___8
 (Term Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_380615e7761919086537a14273a02d22 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple12__item___8@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple12__item___8>

; <Skipped let __proj__Mktuple12__item___8/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple12__item___9>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple12__item___9
 (Term Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_245250918a4432b31aea8152d056489a () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple12__item___9@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple12__item___9>

; <Skipped let __proj__Mktuple12__item___9/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple12__item___10>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple12__item___10
 (Term Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_2a967c8402c441e6d8a9336a7568e4de () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple12__item___10@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple12__item___10>

; <Skipped let __proj__Mktuple12__item___10/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple12__item___11>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple12__item___11
 (Term Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_543c3feac0cd9e04ecb6cfd74ced8964 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple12__item___11@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple12__item___11>

; <Skipped let __proj__Mktuple12__item___11/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple12__item___12>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple12__item___12
 (Term Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_e91029e2320896c60e94f554727a0c41 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple12__item___12@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple12__item___12>

; <Skipped let __proj__Mktuple12__item___12/>

; <Start encoding type FStar.Pervasives.Native.tuple13>
; Constructor
(declare-fun
 FStar.Pervasives.Native.tuple13
 (Term Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
; token
(declare-fun FStar.Pervasives.Native.tuple13@tok () Term)
; Constructor
(declare-fun
 FStar.Pervasives.Native.Mktuple13
 (Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term)
 Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple13__a (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple13__b (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple13__c (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple13__d (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple13__e (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple13__f (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple13__g (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple13__h (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple13__i (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple13__j (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple13__k (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple13__l (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple13__m (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple13__1 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple13__2 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple13__3 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple13__4 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple13__5 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple13__6 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple13__7 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple13__8 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple13__9 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple13__10 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple13__11 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple13__12 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple13__13 (Term) Term)
; data constructor proxy: FStar.Pervasives.Native.Mktuple13
(declare-fun FStar.Pervasives.Native.Mktuple13@tok () Term)
(declare-fun Tm_arrow_6462785e86ca440ee74ed32e1053eae3 () Term)
; <start constructor FStar.Pervasives.Native.tuple13>
; Discriminator definition
(define-fun is-FStar.Pervasives.Native.tuple13 ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 426)
  (exists
    ((@x0 Term)
     (@x1 Term)
     (@x2 Term)
     (@x3 Term)
     (@x4 Term)
     (@x5 Term)
     (@x6 Term)
     (@x7 Term)
     (@x8 Term)
     (@x9 Term)
     (@x10 Term)
     (@x11 Term)
     (@x12 Term))
   (! (=
     __@x0
     (FStar.Pervasives.Native.tuple13 @x0 @x1 @x2 @x3 @x4 @x5 @x6 @x7 @x8 @x9 @x10 @x11 @x12))
    :qid is-FStar.Pervasives.Native.tuple13))))
; </end constructor FStar.Pervasives.Native.tuple13>
; <start constructor FStar.Pervasives.Native.Mktuple13>
; Discriminator definition
(define-fun is-FStar.Pervasives.Native.Mktuple13 ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 433)
  (=
   __@x0
   (FStar.Pervasives.Native.Mktuple13
    (FStar.Pervasives.Native.Mktuple13__a __@x0)
    (FStar.Pervasives.Native.Mktuple13__b __@x0)
    (FStar.Pervasives.Native.Mktuple13__c __@x0)
    (FStar.Pervasives.Native.Mktuple13__d __@x0)
    (FStar.Pervasives.Native.Mktuple13__e __@x0)
    (FStar.Pervasives.Native.Mktuple13__f __@x0)
    (FStar.Pervasives.Native.Mktuple13__g __@x0)
    (FStar.Pervasives.Native.Mktuple13__h __@x0)
    (FStar.Pervasives.Native.Mktuple13__i __@x0)
    (FStar.Pervasives.Native.Mktuple13__j __@x0)
    (FStar.Pervasives.Native.Mktuple13__k __@x0)
    (FStar.Pervasives.Native.Mktuple13__l __@x0)
    (FStar.Pervasives.Native.Mktuple13__m __@x0)
    (FStar.Pervasives.Native.Mktuple13__1 __@x0)
    (FStar.Pervasives.Native.Mktuple13__2 __@x0)
    (FStar.Pervasives.Native.Mktuple13__3 __@x0)
    (FStar.Pervasives.Native.Mktuple13__4 __@x0)
    (FStar.Pervasives.Native.Mktuple13__5 __@x0)
    (FStar.Pervasives.Native.Mktuple13__6 __@x0)
    (FStar.Pervasives.Native.Mktuple13__7 __@x0)
    (FStar.Pervasives.Native.Mktuple13__8 __@x0)
    (FStar.Pervasives.Native.Mktuple13__9 __@x0)
    (FStar.Pervasives.Native.Mktuple13__10 __@x0)
    (FStar.Pervasives.Native.Mktuple13__11 __@x0)
    (FStar.Pervasives.Native.Mktuple13__12 __@x0)
    (FStar.Pervasives.Native.Mktuple13__13 __@x0)))))
; </end constructor FStar.Pervasives.Native.Mktuple13>
; </end encoding type FStar.Pervasives.Native.tuple13>

; <Start encoding assume FStar.Pervasives.Native.tuple13__uu___haseq>
; </end encoding assume FStar.Pervasives.Native.tuple13__uu___haseq>

; <Start encoding val FStar.Pervasives.Native.uu___is_Mktuple13>
(declare-fun
 FStar.Pervasives.Native.uu___is_Mktuple13
 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_68c092e8b387730b412c4dcf592b12d3 () Term)
(declare-fun FStar.Pervasives.Native.uu___is_Mktuple13@tok () Term)
; </end encoding val FStar.Pervasives.Native.uu___is_Mktuple13>

; <Skipped let uu___is_Mktuple13/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple13__item___1>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple13__item___1
 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_82a3dc3a5dbad615d8d4a31db238e43f () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple13__item___1@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple13__item___1>

; <Skipped let __proj__Mktuple13__item___1/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple13__item___2>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple13__item___2
 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_1da976aaa65f1c6b8b256dfc45c41306 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple13__item___2@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple13__item___2>

; <Skipped let __proj__Mktuple13__item___2/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple13__item___3>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple13__item___3
 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_ca5cf529c415deee29e0a34c0c5d1c9f () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple13__item___3@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple13__item___3>

; <Skipped let __proj__Mktuple13__item___3/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple13__item___4>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple13__item___4
 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_94f6c578541b6cb528ca9e7dd1dacc3b () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple13__item___4@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple13__item___4>

; <Skipped let __proj__Mktuple13__item___4/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple13__item___5>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple13__item___5
 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_211e172b7220adc186d8a02ff17e8780 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple13__item___5@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple13__item___5>

; <Skipped let __proj__Mktuple13__item___5/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple13__item___6>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple13__item___6
 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_9276a4f669d8497205e8d59f12da53ba () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple13__item___6@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple13__item___6>

; <Skipped let __proj__Mktuple13__item___6/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple13__item___7>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple13__item___7
 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_8aa8f381a5ed57cbbae9dcd2405ce80f () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple13__item___7@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple13__item___7>

; <Skipped let __proj__Mktuple13__item___7/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple13__item___8>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple13__item___8
 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_51814106613688cf259d7cdba9c24d93 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple13__item___8@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple13__item___8>

; <Skipped let __proj__Mktuple13__item___8/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple13__item___9>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple13__item___9
 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_05fec25e6f03f974bb2933a910642d7e () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple13__item___9@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple13__item___9>

; <Skipped let __proj__Mktuple13__item___9/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple13__item___10>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple13__item___10
 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_3280ee04611a7985c9d107bb1a8a330a () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple13__item___10@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple13__item___10>

; <Skipped let __proj__Mktuple13__item___10/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple13__item___11>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple13__item___11
 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_86c868d5d5058e8e5ec1f4d0285c7e90 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple13__item___11@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple13__item___11>

; <Skipped let __proj__Mktuple13__item___11/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple13__item___12>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple13__item___12
 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_7263c1a3c4475bb4e4b41a1be4bf22da () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple13__item___12@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple13__item___12>

; <Skipped let __proj__Mktuple13__item___12/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple13__item___13>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple13__item___13
 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_338c65ae58844787891c6f47cf01c068 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple13__item___13@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple13__item___13>

; <Skipped let __proj__Mktuple13__item___13/>

; <Start encoding type FStar.Pervasives.Native.tuple14>
; Constructor
(declare-fun
 FStar.Pervasives.Native.tuple14
 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
; token
(declare-fun FStar.Pervasives.Native.tuple14@tok () Term)
; Constructor
(declare-fun
 FStar.Pervasives.Native.Mktuple14
 (Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term
  Term)
 Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__a (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__b (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__c (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__d (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__e (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__f (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__g (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__h (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__i (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__j (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__k (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__l (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__m (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__n (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__1 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__2 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__3 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__4 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__5 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__6 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__7 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__8 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__9 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__10 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__11 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__12 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__13 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Native.Mktuple14__14 (Term) Term)
; data constructor proxy: FStar.Pervasives.Native.Mktuple14
(declare-fun FStar.Pervasives.Native.Mktuple14@tok () Term)
(declare-fun Tm_arrow_484e3bf88a886900f7e695d7333615e9 () Term)
; <start constructor FStar.Pervasives.Native.tuple14>
; Discriminator definition
(define-fun is-FStar.Pervasives.Native.tuple14 ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 465)
  (exists
    ((@x0 Term)
     (@x1 Term)
     (@x2 Term)
     (@x3 Term)
     (@x4 Term)
     (@x5 Term)
     (@x6 Term)
     (@x7 Term)
     (@x8 Term)
     (@x9 Term)
     (@x10 Term)
     (@x11 Term)
     (@x12 Term)
     (@x13 Term))
   (! (=
     __@x0
     (FStar.Pervasives.Native.tuple14 @x0 @x1 @x2 @x3 @x4 @x5 @x6 @x7 @x8 @x9 @x10 @x11 @x12 @x13))
    :qid is-FStar.Pervasives.Native.tuple14))))
; </end constructor FStar.Pervasives.Native.tuple14>
; <start constructor FStar.Pervasives.Native.Mktuple14>
; Discriminator definition
(define-fun is-FStar.Pervasives.Native.Mktuple14 ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 472)
  (=
   __@x0
   (FStar.Pervasives.Native.Mktuple14
    (FStar.Pervasives.Native.Mktuple14__a __@x0)
    (FStar.Pervasives.Native.Mktuple14__b __@x0)
    (FStar.Pervasives.Native.Mktuple14__c __@x0)
    (FStar.Pervasives.Native.Mktuple14__d __@x0)
    (FStar.Pervasives.Native.Mktuple14__e __@x0)
    (FStar.Pervasives.Native.Mktuple14__f __@x0)
    (FStar.Pervasives.Native.Mktuple14__g __@x0)
    (FStar.Pervasives.Native.Mktuple14__h __@x0)
    (FStar.Pervasives.Native.Mktuple14__i __@x0)
    (FStar.Pervasives.Native.Mktuple14__j __@x0)
    (FStar.Pervasives.Native.Mktuple14__k __@x0)
    (FStar.Pervasives.Native.Mktuple14__l __@x0)
    (FStar.Pervasives.Native.Mktuple14__m __@x0)
    (FStar.Pervasives.Native.Mktuple14__n __@x0)
    (FStar.Pervasives.Native.Mktuple14__1 __@x0)
    (FStar.Pervasives.Native.Mktuple14__2 __@x0)
    (FStar.Pervasives.Native.Mktuple14__3 __@x0)
    (FStar.Pervasives.Native.Mktuple14__4 __@x0)
    (FStar.Pervasives.Native.Mktuple14__5 __@x0)
    (FStar.Pervasives.Native.Mktuple14__6 __@x0)
    (FStar.Pervasives.Native.Mktuple14__7 __@x0)
    (FStar.Pervasives.Native.Mktuple14__8 __@x0)
    (FStar.Pervasives.Native.Mktuple14__9 __@x0)
    (FStar.Pervasives.Native.Mktuple14__10 __@x0)
    (FStar.Pervasives.Native.Mktuple14__11 __@x0)
    (FStar.Pervasives.Native.Mktuple14__12 __@x0)
    (FStar.Pervasives.Native.Mktuple14__13 __@x0)
    (FStar.Pervasives.Native.Mktuple14__14 __@x0)))))
; </end constructor FStar.Pervasives.Native.Mktuple14>
; </end encoding type FStar.Pervasives.Native.tuple14>

; <Start encoding assume FStar.Pervasives.Native.tuple14__uu___haseq>
; </end encoding assume FStar.Pervasives.Native.tuple14__uu___haseq>

; <Start encoding val FStar.Pervasives.Native.uu___is_Mktuple14>
(declare-fun
 FStar.Pervasives.Native.uu___is_Mktuple14
 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_2de133cfaca100fc23d8bf4b3421db9a () Term)
(declare-fun FStar.Pervasives.Native.uu___is_Mktuple14@tok () Term)
; </end encoding val FStar.Pervasives.Native.uu___is_Mktuple14>

; <Skipped let uu___is_Mktuple14/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple14__item___1>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple14__item___1
 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_2e3216cab266e138debd68d0a503c177 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple14__item___1@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple14__item___1>

; <Skipped let __proj__Mktuple14__item___1/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple14__item___2>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple14__item___2
 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_958b0270e487d0bf5fe9191b9efaa127 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple14__item___2@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple14__item___2>

; <Skipped let __proj__Mktuple14__item___2/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple14__item___3>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple14__item___3
 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_08349f596f8c0acf60d1587bebe8c91b () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple14__item___3@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple14__item___3>

; <Skipped let __proj__Mktuple14__item___3/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple14__item___4>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple14__item___4
 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_2b069168147ba0f67f117ad5b0ac078b () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple14__item___4@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple14__item___4>

; <Skipped let __proj__Mktuple14__item___4/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple14__item___5>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple14__item___5
 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_1e38bb16245a24a197c44a262fee7bf1 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple14__item___5@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple14__item___5>

; <Skipped let __proj__Mktuple14__item___5/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple14__item___6>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple14__item___6
 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_7a148953a3884454d8a1dffddce086bb () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple14__item___6@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple14__item___6>

; <Skipped let __proj__Mktuple14__item___6/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple14__item___7>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple14__item___7
 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_812eeb3fdab56dfea8e419236740acb0 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple14__item___7@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple14__item___7>

; <Skipped let __proj__Mktuple14__item___7/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple14__item___8>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple14__item___8
 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_9dc932ce7cdfd6fa57f6536787fcb65b () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple14__item___8@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple14__item___8>

; <Skipped let __proj__Mktuple14__item___8/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple14__item___9>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple14__item___9
 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_2600722933f06bc55e28bb3fc2ce4a6a () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple14__item___9@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple14__item___9>

; <Skipped let __proj__Mktuple14__item___9/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple14__item___10>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple14__item___10
 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_f51203e57fd66f9e9293b8962c57edfe () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple14__item___10@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple14__item___10>

; <Skipped let __proj__Mktuple14__item___10/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple14__item___11>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple14__item___11
 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_7c34e0c28edc5fc4ad24d0b749c0adb7 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple14__item___11@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple14__item___11>

; <Skipped let __proj__Mktuple14__item___11/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple14__item___12>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple14__item___12
 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_8772cc50ea320af17b3f2371c273679a () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple14__item___12@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple14__item___12>

; <Skipped let __proj__Mktuple14__item___12/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple14__item___13>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple14__item___13
 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_039da0b9a8da1a651a1c570e55456614 () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple14__item___13@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple14__item___13>

; <Skipped let __proj__Mktuple14__item___13/>

; <Start encoding val FStar.Pervasives.Native.__proj__Mktuple14__item___14>
(declare-fun
 FStar.Pervasives.Native.__proj__Mktuple14__item___14
 (Term Term Term Term Term Term Term Term Term Term Term Term Term Term Term)
 Term)
(declare-fun Tm_arrow_579ada2eb036c15c7306dac5b648153e () Term)
(declare-fun FStar.Pervasives.Native.__proj__Mktuple14__item___14@tok () Term)
; </end encoding val FStar.Pervasives.Native.__proj__Mktuple14__item___14>

; <Skipped let __proj__Mktuple14__item___14/>

; End Externals for module FStar.Pervasives.Native
; Externals for interface FStar.Pervasives
; <Start encoding val FStar.Pervasives.remove_unused_type_parameters>
(declare-fun FStar.Pervasives.remove_unused_type_parameters (Term) Term)

(declare-fun FStar.Pervasives.remove_unused_type_parameters@tok () Term)
; </end encoding val FStar.Pervasives.remove_unused_type_parameters>

; <Start encoding let pattern>
(declare-fun FStar.Pervasives.pattern () Term)
; </end encoding let pattern>

; <Start encoding val FStar.Pervasives.smt_pat>
(declare-fun FStar.Pervasives.smt_pat (Term Term) Term)
(declare-fun Tm_arrow_ce7b692455ad1649f97902066cf7c9aa () Term)
(declare-fun FStar.Pervasives.smt_pat@tok () Term)
; </end encoding val FStar.Pervasives.smt_pat>

; <Start encoding val FStar.Pervasives.smt_pat_or>
(declare-fun FStar.Pervasives.smt_pat_or (Term) Term)
(declare-fun Tm_arrow_cbfaca2770c8ef7d6393b664b7ea1a41 () Term)
(declare-fun FStar.Pervasives.smt_pat_or@tok () Term)
; </end encoding val FStar.Pervasives.smt_pat_or>

; <Start encoding let eqtype_u>
(declare-fun FStar.Pervasives.eqtype_u () Term)

; </end encoding let eqtype_u>

; <Skipped effect FStar.Pervasives.Lemma a pre post pats = Prims.Pure a/>

; <Start encoding val FStar.Pervasives.spinoff>
(declare-fun FStar.Pervasives.spinoff (Term) Term)

(declare-fun FStar.Pervasives.spinoff@tok () Term)
; </end encoding val FStar.Pervasives.spinoff>

; <Start encoding val FStar.Pervasives.spinoff_eq>
; Uninterpreted function symbol for impure function
(declare-fun FStar.Pervasives.spinoff_eq (Term) Term)
; Uninterpreted name for impure function
(declare-fun FStar.Pervasives.spinoff_eq@tok () Term)
; </end encoding val FStar.Pervasives.spinoff_eq>

; <Start encoding val FStar.Pervasives.spinoff_equiv>
; Uninterpreted function symbol for impure function
(declare-fun FStar.Pervasives.spinoff_equiv (Term) Term)
; Uninterpreted name for impure function
(declare-fun FStar.Pervasives.spinoff_equiv@tok () Term)
; </end encoding val FStar.Pervasives.spinoff_equiv>

; <Start encoding val FStar.Pervasives.assert_spinoff>
(declare-fun FStar.Pervasives.assert_spinoff (Term) Term)

(declare-fun Tm_arrow_071538fd1c72fb82c7bb7b280daddf84 () Term)
(declare-fun FStar.Pervasives.assert_spinoff@tok () Term)

; </end encoding val FStar.Pervasives.assert_spinoff>

; <Start encoding let id>
(declare-fun FStar.Pervasives.id (Term Term) Term)

(declare-fun FStar.Pervasives.id@tok () Term)
; </end encoding let id>

; <Start encoding let trivial_pure_post>
(declare-fun FStar.Pervasives.trivial_pure_post (Term) Term)
(declare-fun Tm_arrow_53823f439377767fbcd3e27ebcdb971b () Term)
(declare-fun FStar.Pervasives.trivial_pure_post@tok () Term)

(declare-fun Tm_abs_5e34897418ce4950a4effcc8c159cf53 (Term) Term)
; </end encoding let trivial_pure_post>

; <Start encoding val FStar.Pervasives.ambient>
(declare-fun FStar.Pervasives.ambient (Term Term) Term)
(declare-fun Tm_arrow_9e007179360e2932d75ab29019e3d7fa () Term)
(declare-fun FStar.Pervasives.ambient@tok () Term)
; </end encoding val FStar.Pervasives.ambient>

; <Start encoding val FStar.Pervasives.intro_ambient>
(declare-fun FStar.Pervasives.intro_ambient (Term Term) Term)
(declare-fun Tm_arrow_6fc6334d56387f3d408122a4bd045e7e () Term)
(declare-fun FStar.Pervasives.intro_ambient@tok () Term)
; </end encoding val FStar.Pervasives.intro_ambient>

; <Start encoding val FStar.Pervasives.normalize_term>
(declare-fun FStar.Pervasives.normalize_term (Term Term) Term)

(declare-fun FStar.Pervasives.normalize_term@tok () Term)
; </end encoding val FStar.Pervasives.normalize_term>

; <Start encoding val FStar.Pervasives.normalize>
(declare-fun FStar.Pervasives.normalize (Term) Term)

(declare-fun FStar.Pervasives.normalize@tok () Term)
; </end encoding val FStar.Pervasives.normalize>

; <Start encoding val FStar.Pervasives.norm>
(declare-fun FStar.Pervasives.norm (Term Term Term) Term)
(declare-fun Tm_arrow_aee71d833dbd97a86f5f9c937995d6d6 () Term)
(declare-fun FStar.Pervasives.norm@tok () Term)
; </end encoding val FStar.Pervasives.norm>

; <Start encoding val FStar.Pervasives.assert_norm>
(declare-fun FStar.Pervasives.assert_norm (Term) Term)

(declare-fun Tm_arrow_ee24fcf624d074d3c637ee61e4a867fb () Term)
(declare-fun FStar.Pervasives.assert_norm@tok () Term)

; </end encoding val FStar.Pervasives.assert_norm>

; <Start encoding val FStar.Pervasives.normalize_term_spec>
; Uninterpreted function symbol for impure function
(declare-fun FStar.Pervasives.normalize_term_spec (Term Term) Term)
; Uninterpreted name for impure function
(declare-fun FStar.Pervasives.normalize_term_spec@tok () Term)
; </end encoding val FStar.Pervasives.normalize_term_spec>

; <Start encoding val FStar.Pervasives.normalize_spec>
; Uninterpreted function symbol for impure function
(declare-fun FStar.Pervasives.normalize_spec (Term) Term)
; Uninterpreted name for impure function
(declare-fun FStar.Pervasives.normalize_spec@tok () Term)
; </end encoding val FStar.Pervasives.normalize_spec>

; <Start encoding val FStar.Pervasives.norm_spec>
; Uninterpreted function symbol for impure function
(declare-fun FStar.Pervasives.norm_spec (Term Term Term) Term)
; Uninterpreted name for impure function
(declare-fun FStar.Pervasives.norm_spec@tok () Term)
; </end encoding val FStar.Pervasives.norm_spec>

; <Start encoding let reveal_opaque>
(declare-fun FStar.Pervasives.reveal_opaque (Term Term) Term)
(declare-fun Tm_refine_52210fb5c006e73edd2aa0f64235d467 (Term Term Term) Term)
(declare-fun Tm_arrow_e7c5eabfca000e59482a883faaaa695b (Term Term) Term)
(declare-fun Tm_arrow_5f531e41d6057ccfcfdd7979c0838737 () Term)
(declare-fun FStar.Pervasives.reveal_opaque@tok () Term)


; </end encoding let reveal_opaque>

; <Start encoding let pure_return>
(declare-fun FStar.Pervasives.pure_return (Term Term) Term)
(declare-fun Tm_arrow_0dff8d294aeaf0b1d7e9cad664c9a15f () Term)
(declare-fun FStar.Pervasives.pure_return@tok () Term)

(declare-fun Tm_abs_bc5117f6a06a581c69e04141781c86d0 (Term Term Term) Term)
(declare-fun Tm_arrow_c88a29758356586fc450d481d4b685f3 (Term) Term)
(declare-fun Tm_abs_bdac9a3f32789788b83138a3a4262d0d (Term Term) Term)
; </end encoding let pure_return>

; <Start encoding let pure_bind_wp>
(declare-fun Tm_arrow_c05bc9331677cc1a187ad7677301a601 (Term Term) Term)
(declare-fun FStar.Pervasives.pure_bind_wp (Term Term Term Term) Term)

(declare-fun Tm_arrow_f8eba41a4bcb9aca0e3c11224f695d1e () Term)
(declare-fun FStar.Pervasives.pure_bind_wp@tok () Term)


(declare-fun Tm_abs_d0f415a5361a9d7988d8e425dc193472 (Term Term Term) Term)

(declare-fun Tm_abs_72b65b71b828688dbb0ba657715a194c (Term Term Term Term) Term)
; </end encoding let pure_bind_wp>

; <Start encoding let pure_if_then_else>
(declare-fun FStar.Pervasives.pure_if_then_else (Term Term Term Term) Term)
(declare-fun Tm_arrow_5911c11ab85061b4a8acf6a6ff43aaea () Term)
(declare-fun FStar.Pervasives.pure_if_then_else@tok () Term)

(declare-fun Tm_abs_614d7ab3976dfea6b6428085a93bafcc (Term Term Term Term) Term)
; </end encoding let pure_if_then_else>

; <Start encoding let pure_ite_wp>
(declare-fun FStar.Pervasives.pure_ite_wp (Term Term) Term)
(declare-fun Tm_arrow_983cc9c1e881fffd3b37c61b327d54c8 () Term)
(declare-fun FStar.Pervasives.pure_ite_wp@tok () Term)

(declare-fun Tm_abs_ea1703a99385b474600aa7a3bdb045c5 (Term Term Term) Term)
(declare-fun Tm_arrow_b275e247a67e3e77d7c5997d864d1247 (Term) Term)
(declare-fun Tm_abs_f9993abe3e10fc5902262cf22e5f5e1c (Term Term Term) Term)

(declare-fun Tm_abs_a4d8a67e708eb0f8e41d6eefd90d8b3d (Term Term) Term)
; </end encoding let pure_ite_wp>

; <Start encoding let pure_close_wp>

(declare-fun FStar.Pervasives.pure_close_wp (Term Term Term) Term)

(declare-fun Tm_arrow_6424f17922e38fc8eb3b7ad8d9107d78 () Term)
(declare-fun FStar.Pervasives.pure_close_wp@tok () Term)




(declare-fun Tm_abs_bef01cdc202d648a37f7725a1e8579fa (Term Term Term) Term)
; </end encoding let pure_close_wp>

; <Start encoding let pure_null_wp>
(declare-fun FStar.Pervasives.pure_null_wp (Term) Term)
(declare-fun Tm_arrow_e02f472dad10492b4fdaf21971ae643f () Term)
(declare-fun FStar.Pervasives.pure_null_wp@tok () Term)



(declare-fun Tm_abs_c7a599bd05f6d553477b7b3a5a51d357 (Term) Term)
; </end encoding let pure_null_wp>

; <Start encoding let pure_assert_wp>
(declare-fun FStar.Pervasives.pure_assert_wp (Term) Term)

(declare-fun FStar.Pervasives.pure_assert_wp@tok () Term)
; </end encoding let pure_assert_wp>

; <Start encoding let pure_assume_wp>
(declare-fun FStar.Pervasives.pure_assume_wp (Term) Term)

(declare-fun FStar.Pervasives.pure_assume_wp@tok () Term)
; </end encoding let pure_assume_wp>

; <Skipped new_effect { FStar.Pervasives.DIV ... }/>

; <Skipped sub_effect Prims.PURE ~> FStar.Pervasives.DIV/>

; <Start encoding let div_hoare_to_wp>
(declare-fun FStar.Pervasives.div_hoare_to_wp (Term Term Term) Term)
(declare-fun Tm_arrow_e81e37f60b892c60a4b806bfecd6c240 () Term)
(declare-fun FStar.Pervasives.div_hoare_to_wp@tok () Term)




(declare-fun Tm_abs_69982e78bbdc9cbdfcc98c8c3ec276f1 (Term Term Term Term) Term)


(declare-fun Tm_abs_95829b03554cf2093d2bc29e28500b94 (Term Term Term) Term)
; </end encoding let div_hoare_to_wp>

; <Skipped effect FStar.Pervasives.Div a pre post = FStar.Pervasives.DIV a/>

; <Skipped effect FStar.Pervasives.Dv a = FStar.Pervasives.DIV a/>

; <Skipped effect FStar.Pervasives.EXT a = FStar.Pervasives.Dv a/>

; <Start encoding let st_pre_h>
(declare-fun FStar.Pervasives.st_pre_h (Term) Term)

(declare-fun FStar.Pervasives.st_pre_h@tok () Term)

; </end encoding let st_pre_h>

; <Start encoding let st_post_h'>
(declare-fun FStar.Pervasives.st_post_h_ (Term Term Term) Term)
(declare-fun Tm_arrow_659175ed40df3b798f91ffaee9e689bd () Term)
(declare-fun FStar.Pervasives.st_post_h_@tok () Term)

(declare-fun Tm_arrow_14435f7112db17792f8cd33f8f7ea859 (Term Term Term) Term)
; </end encoding let st_post_h'>

; <Start encoding let st_post_h>
(declare-fun FStar.Pervasives.st_post_h (Term Term) Term)

(declare-fun FStar.Pervasives.st_post_h@tok () Term)
; </end encoding let st_post_h>

; <Start encoding let st_wp_h>
(declare-fun FStar.Pervasives.st_wp_h (Term Term) Term)

(declare-fun FStar.Pervasives.st_wp_h@tok () Term)
(declare-fun Tm_arrow_c80b139653078194d2de90941effdc68 (Term Term) Term)
; </end encoding let st_wp_h>

; <Start encoding let st_return>
(declare-fun FStar.Pervasives.st_return (Term Term Term Term) Term)

(declare-fun Tm_arrow_6bfe4bf6faf1fb53a521d575cefc35ef () Term)
(declare-fun FStar.Pervasives.st_return@tok () Term)

; </end encoding let st_return>

; <Start encoding let st_bind_wp>
(declare-fun Tm_arrow_c6e0af8c2ccbdda79db5c09d07e87e35 (Term Term Term) Term)
(declare-fun FStar.Pervasives.st_bind_wp (Term Term Term Term Term Term Term) Term)

(declare-fun Tm_arrow_0eca50df2f29485bdbf578799f16b4a6 () Term)
(declare-fun FStar.Pervasives.st_bind_wp@tok () Term)

(declare-fun Tm_arrow_eb9b1a038524b37579c152a3f169145e (Term Term) Term)
(declare-fun Tm_abs_0f3b5ee9eaa8de8cacad7d3dcacb4558 (Term Term Term Term) Term)
; </end encoding let st_bind_wp>

; <Start encoding let st_if_then_else>
(declare-fun FStar.Pervasives.st_if_then_else (Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_6e48361e1a1c92df6ec1ff87e622ddad () Term)
(declare-fun FStar.Pervasives.st_if_then_else@tok () Term)
; </end encoding let st_if_then_else>

; <Start encoding let st_ite_wp>
(declare-fun FStar.Pervasives.st_ite_wp (Term Term Term Term Term) Term)
(declare-fun Tm_arrow_eaad896c6afdcb7ade2e80b5a6a930af () Term)
(declare-fun FStar.Pervasives.st_ite_wp@tok () Term)
; </end encoding let st_ite_wp>

; <Start encoding let st_stronger>
(declare-fun FStar.Pervasives.st_stronger (Term Term Term Term) Term)
(declare-fun Tm_arrow_ae4d7f489de84317e0022bf89d45dd95 () Term)
(declare-fun FStar.Pervasives.st_stronger@tok () Term)
; </end encoding let st_stronger>

; <Start encoding let st_close_wp>

(declare-fun FStar.Pervasives.st_close_wp (Term Term Term Term Term Term) Term)

(declare-fun Tm_arrow_de6d3045642382698e9e38d41acfd7cc () Term)
(declare-fun FStar.Pervasives.st_close_wp@tok () Term)

; </end encoding let st_close_wp>

; <Start encoding let st_trivial>
(declare-fun FStar.Pervasives.st_trivial (Term Term Term) Term)
(declare-fun Tm_arrow_f145e04ff3c7033bdfc718f7f5bb1df0 () Term)
(declare-fun FStar.Pervasives.st_trivial@tok () Term)

(declare-fun Tm_abs_89b21c42be5bc00d63e29f63ae20d4e2 (Term Term) Term)
; </end encoding let st_trivial>

; <Skipped new_effect { FStar.Pervasives.STATE_h ... }/>

; <Start encoding type FStar.Pervasives.result>
; Constructor
(declare-fun FStar.Pervasives.result (Term) Term)
; token
(declare-fun FStar.Pervasives.result@tok () Term)
; Constructor
(declare-fun FStar.Pervasives.V (Term Term) Term)
; Projector
(declare-fun FStar.Pervasives.V_a (Term) Term)
; Projector
(declare-fun FStar.Pervasives.V_v (Term) Term)
; data constructor proxy: FStar.Pervasives.V
(declare-fun FStar.Pervasives.V@tok () Term)
; Constructor
(declare-fun FStar.Pervasives.E (Term Term) Term)
; Projector
(declare-fun FStar.Pervasives.E_a (Term) Term)
; Projector
(declare-fun FStar.Pervasives.E_e (Term) Term)
; data constructor proxy: FStar.Pervasives.E
(declare-fun FStar.Pervasives.E@tok () Term)
; Constructor
(declare-fun FStar.Pervasives.Err (Term Term) Term)
; Projector
(declare-fun FStar.Pervasives.Err_a (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Err_msg (Term) Term)
; data constructor proxy: FStar.Pervasives.Err
(declare-fun FStar.Pervasives.Err@tok () Term)
(declare-fun Tm_arrow_30908143640041985b9200e2fb38a259 () Term)
(declare-fun Tm_arrow_f8bb10130fea772e0f786d78a188c381 () Term)
(declare-fun Tm_arrow_93661c87034b0b64c4714dafbe2b02e6 () Term)
; <start constructor FStar.Pervasives.result>
; Discriminator definition
(define-fun is-FStar.Pervasives.result ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 253)
  (exists ((@x0 Term)) (! (= __@x0 (FStar.Pervasives.result @x0)) :qid is-FStar.Pervasives.result))))
; </end constructor FStar.Pervasives.result>
; <start constructor FStar.Pervasives.V>
; Discriminator definition
(define-fun is-FStar.Pervasives.V ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 260)
  (= __@x0 (FStar.Pervasives.V (FStar.Pervasives.V_a __@x0) (FStar.Pervasives.V_v __@x0)))))
; </end constructor FStar.Pervasives.V>
; <start constructor FStar.Pervasives.E>
; Discriminator definition
(define-fun is-FStar.Pervasives.E ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 265)
  (= __@x0 (FStar.Pervasives.E (FStar.Pervasives.E_a __@x0) (FStar.Pervasives.E_e __@x0)))))
; </end constructor FStar.Pervasives.E>
; <start constructor FStar.Pervasives.Err>
; Discriminator definition
(define-fun is-FStar.Pervasives.Err ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 270)
  (= __@x0 (FStar.Pervasives.Err (FStar.Pervasives.Err_a __@x0) (FStar.Pervasives.Err_msg __@x0)))))
; </end constructor FStar.Pervasives.Err>
; </end encoding type FStar.Pervasives.result>

; <Start encoding val FStar.Pervasives.uu___is_V>
(declare-fun FStar.Pervasives.uu___is_V (Term Term) Term)
(declare-fun Tm_arrow_5cd1d0722a6a986faf6f8e557186fe24 () Term)
(declare-fun FStar.Pervasives.uu___is_V@tok () Term)
; </end encoding val FStar.Pervasives.uu___is_V>

; <Skipped let uu___is_V/>

; <Start encoding val FStar.Pervasives.__proj__V__item__v>
(declare-fun Tm_refine_9db520b26a7f39c5a01493a3f375290d (Term) Term)
(declare-fun FStar.Pervasives.__proj__V__item__v (Term Term) Term)

(declare-fun Tm_arrow_1ea119bf213c016916a7095486e28467 () Term)
(declare-fun FStar.Pervasives.__proj__V__item__v@tok () Term)
; </end encoding val FStar.Pervasives.__proj__V__item__v>

; <Skipped let __proj__V__item__v/>

; <Start encoding val FStar.Pervasives.uu___is_E>
(declare-fun FStar.Pervasives.uu___is_E (Term Term) Term)

(declare-fun FStar.Pervasives.uu___is_E@tok () Term)
; </end encoding val FStar.Pervasives.uu___is_E>

; <Skipped let uu___is_E/>

; <Start encoding val FStar.Pervasives.__proj__E__item__e>
(declare-fun Tm_refine_95e1e2ee29104754cc3740f5575fc6e5 (Term) Term)
(declare-fun FStar.Pervasives.__proj__E__item__e (Term Term) Term)

(declare-fun Tm_arrow_19e73c373dbf3f9945c6fcfce8a07661 () Term)
(declare-fun FStar.Pervasives.__proj__E__item__e@tok () Term)
; </end encoding val FStar.Pervasives.__proj__E__item__e>

; <Skipped let __proj__E__item__e/>

; <Start encoding val FStar.Pervasives.uu___is_Err>
(declare-fun FStar.Pervasives.uu___is_Err (Term Term) Term)

(declare-fun FStar.Pervasives.uu___is_Err@tok () Term)
; </end encoding val FStar.Pervasives.uu___is_Err>

; <Skipped let uu___is_Err/>

; <Start encoding val FStar.Pervasives.__proj__Err__item__msg>
(declare-fun Tm_refine_22fb403854eba07427f92e79848f9d9f (Term) Term)
(declare-fun FStar.Pervasives.__proj__Err__item__msg (Term Term) Term)

(declare-fun Tm_arrow_f7e3debb858e412c9497460c5187d5cd () Term)
(declare-fun FStar.Pervasives.__proj__Err__item__msg@tok () Term)
; </end encoding val FStar.Pervasives.__proj__Err__item__msg>

; <Skipped let __proj__Err__item__msg/>

; <Start encoding let ex_pre>
(declare-fun FStar.Pervasives.ex_pre () Term)
; </end encoding let ex_pre>

; <Start encoding let ex_post'>
(declare-fun FStar.Pervasives.ex_post_ (Term Term) Term)

(declare-fun FStar.Pervasives.ex_post_@tok () Term)
(declare-fun Tm_refine_a4dcdeeacbcb04d05a6720f786918fd6 (Term Term) Term)
(declare-fun Tm_arrow_68b66d987e8a7bdf825af8b370553e65 (Term Term) Term)
; </end encoding let ex_post'>

; <Start encoding let ex_post>
(declare-fun FStar.Pervasives.ex_post (Term) Term)

(declare-fun FStar.Pervasives.ex_post@tok () Term)
; </end encoding let ex_post>

; <Start encoding let ex_wp>
(declare-fun FStar.Pervasives.ex_wp (Term) Term)

(declare-fun FStar.Pervasives.ex_wp@tok () Term)
(declare-fun Tm_arrow_58168e52ae0908fefec42cac825ecc69 (Term) Term)
; </end encoding let ex_wp>

; <Start encoding let ex_return>
(declare-fun FStar.Pervasives.ex_return (Term Term Term) Term)
(declare-fun Tm_arrow_375264f6f19b4e37d33ffba9f6b1c7d2 () Term)
(declare-fun FStar.Pervasives.ex_return@tok () Term)
; </end encoding let ex_return>

; <Start encoding let ex_bind_wp>
(declare-fun Tm_arrow_3eb2992a529511f5b0ff2fef4e4594ad (Term Term) Term)
(declare-fun FStar.Pervasives.ex_bind_wp (Term Term Term Term Term) Term)

(declare-fun Tm_arrow_1da2056f1a2fe3dc8db7decf5cbd5885 () Term)
(declare-fun FStar.Pervasives.ex_bind_wp@tok () Term)

(declare-fun Tm_arrow_ca5db633696caf7e0cd44c11654eed8b (Term) Term)
(declare-fun Tm_abs_c1d9037a5cc10cc07ba9b6a7a58728db (Term Term Term Term) Term)
; </end encoding let ex_bind_wp>

; <Start encoding let ex_if_then_else>
(declare-fun FStar.Pervasives.ex_if_then_else (Term Term Term Term Term) Term)
(declare-fun Tm_arrow_08bd7ce530cc6e8b4a3f8dadbd0806b0 () Term)
(declare-fun FStar.Pervasives.ex_if_then_else@tok () Term)
; </end encoding let ex_if_then_else>

; <Start encoding let ex_ite_wp>
(declare-fun FStar.Pervasives.ex_ite_wp (Term Term Term) Term)
(declare-fun Tm_arrow_c2a8c761b16a75376b24262cd8c50369 () Term)
(declare-fun FStar.Pervasives.ex_ite_wp@tok () Term)
; </end encoding let ex_ite_wp>

; <Start encoding let ex_stronger>
(declare-fun FStar.Pervasives.ex_stronger (Term Term Term) Term)
(declare-fun Tm_arrow_1376d97b5d43e7d77d56729e2a3e04af () Term)
(declare-fun FStar.Pervasives.ex_stronger@tok () Term)
; </end encoding let ex_stronger>

; <Start encoding let ex_close_wp>

(declare-fun FStar.Pervasives.ex_close_wp (Term Term Term Term) Term)

(declare-fun Tm_arrow_814af0adff92aa08c5b8b0951bcb1959 () Term)
(declare-fun FStar.Pervasives.ex_close_wp@tok () Term)

; </end encoding let ex_close_wp>

; <Start encoding let ex_trivial>
(declare-fun FStar.Pervasives.ex_trivial (Term Term) Term)
(declare-fun Tm_arrow_ee4a787765920b0cb4357a47a0d3ac5c () Term)
(declare-fun FStar.Pervasives.ex_trivial@tok () Term)

(declare-fun Tm_abs_5cc223716d095f4545f0dcc745acad5d (Term) Term)
; </end encoding let ex_trivial>

; <Skipped new_effect { FStar.Pervasives.EXN ... }/>

; <Skipped effect FStar.Pervasives.Exn a pre post = FStar.Pervasives.EXN a/>

; <Start encoding let lift_div_exn>
(declare-fun FStar.Pervasives.lift_div_exn (Term Term Term) Term)
(declare-fun Tm_arrow_8196682216f286f6fe3a7dffb3de7d02 () Term)
(declare-fun FStar.Pervasives.lift_div_exn@tok () Term)

(declare-fun Tm_abs_c2b605ddd5d1991642baf5762d2b1dc5 (Term Term) Term)
; </end encoding let lift_div_exn>

; <Skipped sub_effect FStar.Pervasives.DIV ~> FStar.Pervasives.EXN/>

; <Skipped effect FStar.Pervasives.Ex a = FStar.Pervasives.Exn a/>

; <Start encoding let all_pre_h>
(declare-fun FStar.Pervasives.all_pre_h (Term) Term)

(declare-fun FStar.Pervasives.all_pre_h@tok () Term)

; </end encoding let all_pre_h>

; <Start encoding let all_post_h'>
(declare-fun FStar.Pervasives.all_post_h_ (Term Term Term) Term)

(declare-fun FStar.Pervasives.all_post_h_@tok () Term)

(declare-fun Tm_arrow_fc269489cb2e24a10c7710a1f7f9d269 (Term Term Term) Term)
; </end encoding let all_post_h'>

; <Start encoding let all_post_h>
(declare-fun FStar.Pervasives.all_post_h (Term Term) Term)

(declare-fun FStar.Pervasives.all_post_h@tok () Term)
; </end encoding let all_post_h>

; <Start encoding let all_wp_h>
(declare-fun FStar.Pervasives.all_wp_h (Term Term) Term)

(declare-fun FStar.Pervasives.all_wp_h@tok () Term)
(declare-fun Tm_arrow_1cd90c71d90a216d9fb0ba0321a1d3b5 (Term Term) Term)
; </end encoding let all_wp_h>

; <Start encoding let all_return>
(declare-fun FStar.Pervasives.all_return (Term Term Term Term) Term)

(declare-fun Tm_arrow_3f61557667800fb54cc62e48a5201f9d () Term)
(declare-fun FStar.Pervasives.all_return@tok () Term)

; </end encoding let all_return>

; <Start encoding let all_bind_wp>
(declare-fun Tm_arrow_b567b509414635f00096b9b1c3e30b57 (Term Term Term) Term)
(declare-fun FStar.Pervasives.all_bind_wp (Term Term Term Term Term Term Term) Term)

(declare-fun Tm_arrow_6ac18e25eb49f55ae0ce9c14679ecc22 () Term)
(declare-fun FStar.Pervasives.all_bind_wp@tok () Term)

(declare-fun Tm_arrow_59cac8a9b1ae3aa9511b8a867f8e934e (Term Term) Term)
(declare-fun Tm_abs_35ddc99cefc0079215f6f6ab3c58856d (Term Term Term Term Term) Term)
; </end encoding let all_bind_wp>

; <Start encoding let all_if_then_else>
(declare-fun FStar.Pervasives.all_if_then_else (Term Term Term Term Term Term Term) Term)
(declare-fun Tm_arrow_491eee2c8dc4eab4d420326a8285d2c4 () Term)
(declare-fun FStar.Pervasives.all_if_then_else@tok () Term)
; </end encoding let all_if_then_else>

; <Start encoding let all_ite_wp>
(declare-fun FStar.Pervasives.all_ite_wp (Term Term Term Term Term) Term)
(declare-fun Tm_arrow_20fdb4e6d0c32f949f55e39a059913a7 () Term)
(declare-fun FStar.Pervasives.all_ite_wp@tok () Term)
; </end encoding let all_ite_wp>

; <Start encoding let all_stronger>
(declare-fun FStar.Pervasives.all_stronger (Term Term Term Term) Term)
(declare-fun Tm_arrow_073b21d0ec8edf2dda32907b45ec5f68 () Term)
(declare-fun FStar.Pervasives.all_stronger@tok () Term)
; </end encoding let all_stronger>

; <Start encoding let all_close_wp>

(declare-fun FStar.Pervasives.all_close_wp (Term Term Term Term Term Term) Term)

(declare-fun Tm_arrow_803d195802308e8beadf04438d3a6508 () Term)
(declare-fun FStar.Pervasives.all_close_wp@tok () Term)

; </end encoding let all_close_wp>

; <Start encoding let all_trivial>
(declare-fun FStar.Pervasives.all_trivial (Term Term Term) Term)
(declare-fun Tm_arrow_957927b0d25001784693eee8b2182308 () Term)
(declare-fun FStar.Pervasives.all_trivial@tok () Term)

(declare-fun Tm_abs_22e463dbd987016e31d6bc67025a7cd9 (Term Term) Term)
; </end encoding let all_trivial>

; <Skipped new_effect { FStar.Pervasives.ALL_h ... }/>

; <Start encoding val FStar.Pervasives.inversion>
(declare-fun FStar.Pervasives.inversion (Term) Term)

(declare-fun FStar.Pervasives.inversion@tok () Term)
; </end encoding val FStar.Pervasives.inversion>

; <Start encoding val FStar.Pervasives.allow_inversion>
(declare-fun FStar.Pervasives.allow_inversion (Term) Term)
(declare-fun Tm_refine_363615bee79fae5066b7c8bd06c286d0 (Term) Term)
(declare-fun Tm_arrow_bcab9cce464ec0f76562bc48c17ba410 () Term)
(declare-fun FStar.Pervasives.allow_inversion@tok () Term)

; </end encoding val FStar.Pervasives.allow_inversion>

; <Start encoding val FStar.Pervasives.invertOption>
; Uninterpreted function symbol for impure function
(declare-fun FStar.Pervasives.invertOption (Term) Term)
; Uninterpreted name for impure function
(declare-fun FStar.Pervasives.invertOption@tok () Term)
; </end encoding val FStar.Pervasives.invertOption>

; <Start encoding type FStar.Pervasives.either>
; Constructor
(declare-fun FStar.Pervasives.either (Term Term) Term)
; token
(declare-fun FStar.Pervasives.either@tok () Term)
; Constructor
(declare-fun FStar.Pervasives.Inl (Term Term Term) Term)
; Projector
(declare-fun FStar.Pervasives.Inl_a (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Inl_b (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Inl_v (Term) Term)
; data constructor proxy: FStar.Pervasives.Inl
(declare-fun FStar.Pervasives.Inl@tok () Term)
; Constructor
(declare-fun FStar.Pervasives.Inr (Term Term Term) Term)
; Projector
(declare-fun FStar.Pervasives.Inr_a (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Inr_b (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Inr_v (Term) Term)
; data constructor proxy: FStar.Pervasives.Inr
(declare-fun FStar.Pervasives.Inr@tok () Term)
(declare-fun Tm_arrow_065da0adeba0c4ae0da1476ececee84c () Term)
(declare-fun Tm_arrow_c883938642e6d97d79c975d8d94b4aac () Term)
; <start constructor FStar.Pervasives.either>
; Discriminator definition
(define-fun is-FStar.Pervasives.either ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 392)
  (exists ((@x0 Term) (@x1 Term))
   (! (= __@x0 (FStar.Pervasives.either @x0 @x1)) :qid is-FStar.Pervasives.either))))
; </end constructor FStar.Pervasives.either>
; <start constructor FStar.Pervasives.Inl>
; Discriminator definition
(define-fun is-FStar.Pervasives.Inl ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 399)
  (=
   __@x0
   (FStar.Pervasives.Inl
    (FStar.Pervasives.Inl_a __@x0)
    (FStar.Pervasives.Inl_b __@x0)
    (FStar.Pervasives.Inl_v __@x0)))))
; </end constructor FStar.Pervasives.Inl>
; <start constructor FStar.Pervasives.Inr>
; Discriminator definition
(define-fun is-FStar.Pervasives.Inr ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 404)
  (=
   __@x0
   (FStar.Pervasives.Inr
    (FStar.Pervasives.Inr_a __@x0)
    (FStar.Pervasives.Inr_b __@x0)
    (FStar.Pervasives.Inr_v __@x0)))))
; </end constructor FStar.Pervasives.Inr>
; </end encoding type FStar.Pervasives.either>

; <Start encoding assume FStar.Pervasives.either__uu___haseq>
; </end encoding assume FStar.Pervasives.either__uu___haseq>

; <Start encoding val FStar.Pervasives.uu___is_Inl>
(declare-fun FStar.Pervasives.uu___is_Inl (Term Term Term) Term)
(declare-fun Tm_arrow_af0c68f1e39d4d6020c0873b16730c7d () Term)
(declare-fun FStar.Pervasives.uu___is_Inl@tok () Term)
; </end encoding val FStar.Pervasives.uu___is_Inl>

; <Skipped let uu___is_Inl/>

; <Start encoding val FStar.Pervasives.__proj__Inl__item__v>
(declare-fun Tm_refine_85e0cc884f8457202f90cd77f23733ba (Term Term) Term)
(declare-fun FStar.Pervasives.__proj__Inl__item__v (Term Term Term) Term)

(declare-fun Tm_arrow_a80e0750277867ba1a434ad3bba8702d () Term)
(declare-fun FStar.Pervasives.__proj__Inl__item__v@tok () Term)
; </end encoding val FStar.Pervasives.__proj__Inl__item__v>

; <Skipped let __proj__Inl__item__v/>

; <Start encoding val FStar.Pervasives.uu___is_Inr>
(declare-fun FStar.Pervasives.uu___is_Inr (Term Term Term) Term)

(declare-fun FStar.Pervasives.uu___is_Inr@tok () Term)
; </end encoding val FStar.Pervasives.uu___is_Inr>

; <Skipped let uu___is_Inr/>

; <Start encoding val FStar.Pervasives.__proj__Inr__item__v>
(declare-fun Tm_refine_8f1f5f564dae90240db429de2eb41517 (Term Term) Term)
(declare-fun FStar.Pervasives.__proj__Inr__item__v (Term Term Term) Term)

(declare-fun Tm_arrow_df618db6b42762940f198036c8a56200 () Term)
(declare-fun FStar.Pervasives.__proj__Inr__item__v@tok () Term)
; </end encoding val FStar.Pervasives.__proj__Inr__item__v>

; <Skipped let __proj__Inr__item__v/>

; <Start encoding let dfst>

(declare-fun FStar.Pervasives.dfst (Term Term Term) Term)


(declare-fun FStar.Pervasives.dfst@tok () Term)

; </end encoding let dfst>

; <Start encoding let dsnd>

(declare-fun FStar.Pervasives.dsnd (Term Term Term) Term)


(declare-fun FStar.Pervasives.dsnd@tok () Term)

; </end encoding let dsnd>

; <Start encoding type FStar.Pervasives.dtuple3>
; Constructor
(declare-fun FStar.Pervasives.dtuple3 (Term Term Term) Term)
; token
(declare-fun FStar.Pervasives.dtuple3@tok () Term)
; Constructor
(declare-fun FStar.Pervasives.Mkdtuple3 (Term Term Term Term Term Term) Term)
; Projector
(declare-fun FStar.Pervasives.Mkdtuple3_a (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Mkdtuple3_b (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Mkdtuple3_c (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Mkdtuple3__1 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Mkdtuple3__2 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Mkdtuple3__3 (Term) Term)
; data constructor proxy: FStar.Pervasives.Mkdtuple3
(declare-fun FStar.Pervasives.Mkdtuple3@tok () Term)

(declare-fun Tm_arrow_0b6559e6ff3addf84b0c2880affbb335 (Term Term) Term)




(declare-fun Tm_arrow_8423f67df62f9e824c55756f9e26058d () Term)
; <start constructor FStar.Pervasives.dtuple3>
; Discriminator definition
(define-fun is-FStar.Pervasives.dtuple3 ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 440)
  (exists ((@x0 Term) (@x1 Term) (@x2 Term))
   (! (= __@x0 (FStar.Pervasives.dtuple3 @x0 @x1 @x2)) :qid is-FStar.Pervasives.dtuple3))))
; </end constructor FStar.Pervasives.dtuple3>
; <start constructor FStar.Pervasives.Mkdtuple3>
; Discriminator definition
(define-fun is-FStar.Pervasives.Mkdtuple3 ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 451)
  (=
   __@x0
   (FStar.Pervasives.Mkdtuple3
    (FStar.Pervasives.Mkdtuple3_a __@x0)
    (FStar.Pervasives.Mkdtuple3_b __@x0)
    (FStar.Pervasives.Mkdtuple3_c __@x0)
    (FStar.Pervasives.Mkdtuple3__1 __@x0)
    (FStar.Pervasives.Mkdtuple3__2 __@x0)
    (FStar.Pervasives.Mkdtuple3__3 __@x0)))))
; </end constructor FStar.Pervasives.Mkdtuple3>
; </end encoding type FStar.Pervasives.dtuple3>

; <Start encoding assume FStar.Pervasives.dtuple3__uu___haseq>


; </end encoding assume FStar.Pervasives.dtuple3__uu___haseq>

; <Start encoding val FStar.Pervasives.uu___is_Mkdtuple3>


(declare-fun FStar.Pervasives.uu___is_Mkdtuple3 (Term Term Term Term) Term)


(declare-fun Tm_arrow_70452cb82cd0a282ca9a2dbeb54c1b04 () Term)
(declare-fun FStar.Pervasives.uu___is_Mkdtuple3@tok () Term)
; </end encoding val FStar.Pervasives.uu___is_Mkdtuple3>

; <Skipped let uu___is_Mkdtuple3/>

; <Start encoding val FStar.Pervasives.__proj__Mkdtuple3__item___1>


(declare-fun FStar.Pervasives.__proj__Mkdtuple3__item___1 (Term Term Term Term) Term)


(declare-fun Tm_arrow_255f0cfe499b1d2e9836e157bce1dba3 () Term)
(declare-fun FStar.Pervasives.__proj__Mkdtuple3__item___1@tok () Term)
; </end encoding val FStar.Pervasives.__proj__Mkdtuple3__item___1>

; <Skipped let __proj__Mkdtuple3__item___1/>

; <Start encoding val FStar.Pervasives.__proj__Mkdtuple3__item___2>


(declare-fun FStar.Pervasives.__proj__Mkdtuple3__item___2 (Term Term Term Term) Term)


(declare-fun Tm_arrow_ea1ded11f7d194a26e812f407333a011 () Term)
(declare-fun FStar.Pervasives.__proj__Mkdtuple3__item___2@tok () Term)
; </end encoding val FStar.Pervasives.__proj__Mkdtuple3__item___2>

; <Skipped let __proj__Mkdtuple3__item___2/>

; <Start encoding val FStar.Pervasives.__proj__Mkdtuple3__item___3>


(declare-fun FStar.Pervasives.__proj__Mkdtuple3__item___3 (Term Term Term Term) Term)


(declare-fun Tm_arrow_1d7ad5cfa0fff643640e3f74466d283e () Term)
(declare-fun FStar.Pervasives.__proj__Mkdtuple3__item___3@tok () Term)
; </end encoding val FStar.Pervasives.__proj__Mkdtuple3__item___3>

; <Skipped let __proj__Mkdtuple3__item___3/>

; <Start encoding type FStar.Pervasives.dtuple4>
; Constructor
(declare-fun FStar.Pervasives.dtuple4 (Term Term Term Term) Term)
; token
(declare-fun FStar.Pervasives.dtuple4@tok () Term)
; Constructor
(declare-fun FStar.Pervasives.Mkdtuple4 (Term Term Term Term Term Term Term Term) Term)
; Projector
(declare-fun FStar.Pervasives.Mkdtuple4_a (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Mkdtuple4_b (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Mkdtuple4_c (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Mkdtuple4_d (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Mkdtuple4__1 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Mkdtuple4__2 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Mkdtuple4__3 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Mkdtuple4__4 (Term) Term)
; data constructor proxy: FStar.Pervasives.Mkdtuple4
(declare-fun FStar.Pervasives.Mkdtuple4@tok () Term)


(declare-fun Tm_arrow_af8eda99ba3685403be22a88669dcb35 (Term Term Term) Term)






(declare-fun Tm_arrow_cef44a6056754f192c2446237c4c1408 () Term)
; <start constructor FStar.Pervasives.dtuple4>
; Discriminator definition
(define-fun is-FStar.Pervasives.dtuple4 ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 509)
  (exists ((@x0 Term) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (= __@x0 (FStar.Pervasives.dtuple4 @x0 @x1 @x2 @x3)) :qid is-FStar.Pervasives.dtuple4))))
; </end constructor FStar.Pervasives.dtuple4>
; <start constructor FStar.Pervasives.Mkdtuple4>
; Discriminator definition
(define-fun is-FStar.Pervasives.Mkdtuple4 ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 522)
  (=
   __@x0
   (FStar.Pervasives.Mkdtuple4
    (FStar.Pervasives.Mkdtuple4_a __@x0)
    (FStar.Pervasives.Mkdtuple4_b __@x0)
    (FStar.Pervasives.Mkdtuple4_c __@x0)
    (FStar.Pervasives.Mkdtuple4_d __@x0)
    (FStar.Pervasives.Mkdtuple4__1 __@x0)
    (FStar.Pervasives.Mkdtuple4__2 __@x0)
    (FStar.Pervasives.Mkdtuple4__3 __@x0)
    (FStar.Pervasives.Mkdtuple4__4 __@x0)))))
; </end constructor FStar.Pervasives.Mkdtuple4>
; </end encoding type FStar.Pervasives.dtuple4>

; <Start encoding assume FStar.Pervasives.dtuple4__uu___haseq>



; </end encoding assume FStar.Pervasives.dtuple4__uu___haseq>

; <Start encoding val FStar.Pervasives.uu___is_Mkdtuple4>



(declare-fun FStar.Pervasives.uu___is_Mkdtuple4 (Term Term Term Term Term) Term)



(declare-fun Tm_arrow_76a226dc2cea2ddd4e4258637fc95e5b () Term)
(declare-fun FStar.Pervasives.uu___is_Mkdtuple4@tok () Term)
; </end encoding val FStar.Pervasives.uu___is_Mkdtuple4>

; <Skipped let uu___is_Mkdtuple4/>

; <Start encoding val FStar.Pervasives.__proj__Mkdtuple4__item___1>



(declare-fun FStar.Pervasives.__proj__Mkdtuple4__item___1 (Term Term Term Term Term) Term)



(declare-fun Tm_arrow_1da4d60ab69f411b912e76cc25e77965 () Term)
(declare-fun FStar.Pervasives.__proj__Mkdtuple4__item___1@tok () Term)
; </end encoding val FStar.Pervasives.__proj__Mkdtuple4__item___1>

; <Skipped let __proj__Mkdtuple4__item___1/>

; <Start encoding val FStar.Pervasives.__proj__Mkdtuple4__item___2>



(declare-fun FStar.Pervasives.__proj__Mkdtuple4__item___2 (Term Term Term Term Term) Term)



(declare-fun Tm_arrow_a86867091548f3d7d3ca1cb8b0458b9f () Term)
(declare-fun FStar.Pervasives.__proj__Mkdtuple4__item___2@tok () Term)
; </end encoding val FStar.Pervasives.__proj__Mkdtuple4__item___2>

; <Skipped let __proj__Mkdtuple4__item___2/>

; <Start encoding val FStar.Pervasives.__proj__Mkdtuple4__item___3>



(declare-fun FStar.Pervasives.__proj__Mkdtuple4__item___3 (Term Term Term Term Term) Term)



(declare-fun Tm_arrow_ee72552fcc293405aa0e854ba26f27ac () Term)
(declare-fun FStar.Pervasives.__proj__Mkdtuple4__item___3@tok () Term)
; </end encoding val FStar.Pervasives.__proj__Mkdtuple4__item___3>

; <Skipped let __proj__Mkdtuple4__item___3/>

; <Start encoding val FStar.Pervasives.__proj__Mkdtuple4__item___4>



(declare-fun FStar.Pervasives.__proj__Mkdtuple4__item___4 (Term Term Term Term Term) Term)



(declare-fun Tm_arrow_6c79def96aa5d5d9eb9555c48dd9ebb6 () Term)
(declare-fun FStar.Pervasives.__proj__Mkdtuple4__item___4@tok () Term)
; </end encoding val FStar.Pervasives.__proj__Mkdtuple4__item___4>

; <Skipped let __proj__Mkdtuple4__item___4/>

; <Start encoding type FStar.Pervasives.dtuple5>
; Constructor
(declare-fun FStar.Pervasives.dtuple5 (Term Term Term Term Term) Term)
; token
(declare-fun FStar.Pervasives.dtuple5@tok () Term)
; Constructor
(declare-fun FStar.Pervasives.Mkdtuple5 (Term Term Term Term Term Term Term Term Term Term) Term)
; Projector
(declare-fun FStar.Pervasives.Mkdtuple5_a (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Mkdtuple5_b (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Mkdtuple5_c (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Mkdtuple5_d (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Mkdtuple5_e (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Mkdtuple5__1 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Mkdtuple5__2 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Mkdtuple5__3 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Mkdtuple5__4 (Term) Term)
; Projector
(declare-fun FStar.Pervasives.Mkdtuple5__5 (Term) Term)
; data constructor proxy: FStar.Pervasives.Mkdtuple5
(declare-fun FStar.Pervasives.Mkdtuple5@tok () Term)



(declare-fun Tm_arrow_e2051b23ee191036cd2c8f08b57577cc (Term Term Term Term) Term)








(declare-fun Tm_arrow_7c47a0b67fa3d6e69e51a1ade2982e74 () Term)
; <start constructor FStar.Pervasives.dtuple5>
; Discriminator definition
(define-fun is-FStar.Pervasives.dtuple5 ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 616)
  (exists ((@x0 Term) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term))
   (! (= __@x0 (FStar.Pervasives.dtuple5 @x0 @x1 @x2 @x3 @x4)) :qid is-FStar.Pervasives.dtuple5))))
; </end constructor FStar.Pervasives.dtuple5>
; <start constructor FStar.Pervasives.Mkdtuple5>
; Discriminator definition
(define-fun is-FStar.Pervasives.Mkdtuple5 ((__@x0 Term)) Bool
 (and
  (= (Term_constr_id __@x0) 631)
  (=
   __@x0
   (FStar.Pervasives.Mkdtuple5
    (FStar.Pervasives.Mkdtuple5_a __@x0)
    (FStar.Pervasives.Mkdtuple5_b __@x0)
    (FStar.Pervasives.Mkdtuple5_c __@x0)
    (FStar.Pervasives.Mkdtuple5_d __@x0)
    (FStar.Pervasives.Mkdtuple5_e __@x0)
    (FStar.Pervasives.Mkdtuple5__1 __@x0)
    (FStar.Pervasives.Mkdtuple5__2 __@x0)
    (FStar.Pervasives.Mkdtuple5__3 __@x0)
    (FStar.Pervasives.Mkdtuple5__4 __@x0)
    (FStar.Pervasives.Mkdtuple5__5 __@x0)))))
; </end constructor FStar.Pervasives.Mkdtuple5>
; </end encoding type FStar.Pervasives.dtuple5>

; <Start encoding assume FStar.Pervasives.dtuple5__uu___haseq>




; </end encoding assume FStar.Pervasives.dtuple5__uu___haseq>

; <Start encoding val FStar.Pervasives.uu___is_Mkdtuple5>




(declare-fun FStar.Pervasives.uu___is_Mkdtuple5 (Term Term Term Term Term Term) Term)




(declare-fun Tm_arrow_790317d9d2afaf2417875fd8f65cee9f () Term)
(declare-fun FStar.Pervasives.uu___is_Mkdtuple5@tok () Term)
; </end encoding val FStar.Pervasives.uu___is_Mkdtuple5>

; <Skipped let uu___is_Mkdtuple5/>

; <Start encoding val FStar.Pervasives.__proj__Mkdtuple5__item___1>




(declare-fun FStar.Pervasives.__proj__Mkdtuple5__item___1 (Term Term Term Term Term Term) Term)




(declare-fun Tm_arrow_855676d3a54fc2cdf0dfa3ac2f15fdad () Term)
(declare-fun FStar.Pervasives.__proj__Mkdtuple5__item___1@tok () Term)
; </end encoding val FStar.Pervasives.__proj__Mkdtuple5__item___1>

; <Skipped let __proj__Mkdtuple5__item___1/>

; <Start encoding val FStar.Pervasives.__proj__Mkdtuple5__item___2>




(declare-fun FStar.Pervasives.__proj__Mkdtuple5__item___2 (Term Term Term Term Term Term) Term)




(declare-fun Tm_arrow_3c181aa1af161d84af20412908ff5981 () Term)
(declare-fun FStar.Pervasives.__proj__Mkdtuple5__item___2@tok () Term)
; </end encoding val FStar.Pervasives.__proj__Mkdtuple5__item___2>

; <Skipped let __proj__Mkdtuple5__item___2/>

; <Start encoding val FStar.Pervasives.__proj__Mkdtuple5__item___3>




(declare-fun FStar.Pervasives.__proj__Mkdtuple5__item___3 (Term Term Term Term Term Term) Term)




(declare-fun Tm_arrow_cc152ea4c314cfd6854de94e70041031 () Term)
(declare-fun FStar.Pervasives.__proj__Mkdtuple5__item___3@tok () Term)
; </end encoding val FStar.Pervasives.__proj__Mkdtuple5__item___3>

; <Skipped let __proj__Mkdtuple5__item___3/>

; <Start encoding val FStar.Pervasives.__proj__Mkdtuple5__item___4>




(declare-fun FStar.Pervasives.__proj__Mkdtuple5__item___4 (Term Term Term Term Term Term) Term)




(declare-fun Tm_arrow_6a05465acf4f8d1b8f43fd30077a772a () Term)
(declare-fun FStar.Pervasives.__proj__Mkdtuple5__item___4@tok () Term)
; </end encoding val FStar.Pervasives.__proj__Mkdtuple5__item___4>

; <Skipped let __proj__Mkdtuple5__item___4/>

; <Start encoding val FStar.Pervasives.__proj__Mkdtuple5__item___5>




(declare-fun FStar.Pervasives.__proj__Mkdtuple5__item___5 (Term Term Term Term Term Term) Term)




(declare-fun Tm_arrow_d5d61b48d54646c5c411627b3a20c98f () Term)
(declare-fun FStar.Pervasives.__proj__Mkdtuple5__item___5@tok () Term)
; </end encoding val FStar.Pervasives.__proj__Mkdtuple5__item___5>

; <Skipped let __proj__Mkdtuple5__item___5/>

; <Start encoding let ignore>
(declare-fun FStar.Pervasives.ignore (Term Term) Term)

(declare-fun FStar.Pervasives.ignore@tok () Term)
; </end encoding let ignore>

; <Start encoding val FStar.Pervasives.false_elim>
(declare-fun Tm_refine_f1ecc6ab6882a651504f328937700647 () Term)
(declare-fun FStar.Pervasives.false_elim (Term Term) Term)

(declare-fun Tm_arrow_7636fbfab5cd88ba06f60c10ea8caef2 () Term)
(declare-fun FStar.Pervasives.false_elim@tok () Term)
; </end encoding val FStar.Pervasives.false_elim>

; <Start encoding val FStar.Pervasives.singleton>
(declare-fun FStar.Pervasives.singleton (Term Term) Term)
(declare-fun Tm_refine_2fbd657fe85bcb2423f9c7e5f9b3bcb5 (Term Term) Term)
(declare-fun Tm_arrow_9cdb4ebd85da757e86217b6fb07ef9fc () Term)
(declare-fun FStar.Pervasives.singleton@tok () Term)

; </end encoding val FStar.Pervasives.singleton>

; <Start encoding let eqtype_as_type>
(declare-fun FStar.Pervasives.eqtype_as_type (Term) Term)
(declare-fun Tm_arrow_7e9afc6da5407011473323ad80ff51bf () Term)
(declare-fun FStar.Pervasives.eqtype_as_type@tok () Term)
; </end encoding let eqtype_as_type>

; <Start encoding let coerce_eq>
(declare-fun Tm_refine_0dee8cb03258a67c2f7ec66427696212 (Term Term) Term)
(declare-fun FStar.Pervasives.coerce_eq (Term Term Term Term) Term)

(declare-fun Tm_arrow_f44173fb14fa6046eedce5f32cb8aae8 () Term)
(declare-fun FStar.Pervasives.coerce_eq@tok () Term)

; </end encoding let coerce_eq>

; <Start encoding val FStar.Pervasives.normalize_for_extraction>
(declare-fun FStar.Pervasives.normalize_for_extraction (Term) Term)
(declare-fun Tm_arrow_20fe1cac894a118b448754808ccf04f5 () Term)
(declare-fun FStar.Pervasives.normalize_for_extraction@tok () Term)
; </end encoding val FStar.Pervasives.normalize_for_extraction>

; <Start encoding val FStar.Pervasives.normalize_for_extraction_type>
(declare-fun FStar.Pervasives.normalize_for_extraction_type (Dummy_sort) Term)
; </end encoding val FStar.Pervasives.normalize_for_extraction_type>

; End Externals for interface FStar.Pervasives
; Externals for interface FStar.Prelude
; End Externals for interface FStar.Prelude
; Externals for module FStar.Mul
; <Start encoding let op_Star>
(declare-fun FStar.Mul.op_Star (Term Term) Term)

(declare-fun FStar.Mul.op_Star@tok () Term)
; </end encoding let op_Star>

; End Externals for module FStar.Mul
(push) ;; push{1
; Internals for Clase01
; encoding sigelt let suma
; <Start encoding let suma>
(declare-fun Clase01.suma (Term Term) Term)

(declare-fun Clase01.suma@tok () Term)
; </end encoding let suma>

; function token typing
;;; Fact-ids: Name Prims.__cache_version_number__; Namespace Prims
(assert
 (! (HasType Prims.__cache_version_number__ Prims.int)
  :named function_token_typing_Prims.__cache_version_number__))
; unit typing
;;; Fact-ids: Name Prims.unit; Namespace Prims
(assert
 (! (HasType Tm_unit Prims.unit) :named unit_typing))
; unit inversion
;;; Fact-ids: Name Prims.unit; Namespace Prims
(assert
 (! (forall ((@u0 Fuel) (@x1 Term))
   (! (implies (HasTypeFuel @u0 @x1 Prims.unit) (= @x1 Tm_unit))
    :pattern ((HasTypeFuel @u0 @x1 Prims.unit))
    :qid unit_inversion))
  :named unit_inversion))
; free var typing
;;; Fact-ids: Name Prims.unit; Namespace Prims
(assert
 (! (HasType Prims.unit Prims.eqtype) :named typing_Prims.unit))
; free var typing
;;; Fact-ids: Name Prims.subtype_of; Namespace Prims
(assert
 (! ;; def=Prims.fst(299,4-299,14); use=Prims.fst(299,4-299,14)
  (forall ((@x0 Term) (@x1 Term))
   (! (implies
     (and (HasType @x0 Tm_type) (HasType @x1 Tm_type))
     (HasType (Prims.subtype_of @x0 @x1) Prims.logical))
    :pattern ((Prims.subtype_of @x0 @x1))
    :qid typing_Prims.subtype_of))
  :named typing_Prims.subtype_of))
; free var typing
;;; Fact-ids: Name Prims.nat; Namespace Prims
(assert
 (! (HasType Prims.nat Tm_type) :named typing_Prims.nat))
; free var typing
;;; Fact-ids: Name Prims.logical; Namespace Prims
(assert
 (! (HasType Prims.logical Tm_type) :named typing_Prims.logical))
; free var typing
;;; Fact-ids: Name Prims.int; Namespace Prims
(assert
 (! (HasType Prims.int Prims.eqtype) :named typing_Prims.int))
; free var typing
;;; Fact-ids: Name Prims.hasEq; Namespace Prims
(assert
 (! ;; def=Prims.fst(77,5-77,10); use=Prims.fst(77,5-77,10)
  (forall ((@x0 Term))
   (! (implies (HasType @x0 Tm_type) (HasType (Prims.hasEq @x0) Tm_type))
    :pattern ((Prims.hasEq @x0))
    :qid typing_Prims.hasEq))
  :named typing_Prims.hasEq))
; free var typing
;;; Fact-ids: Name Prims.eqtype; Namespace Prims
(assert
 (! (HasType Prims.eqtype Tm_type) :named typing_Prims.eqtype))
; free var typing
;;; Fact-ids: Name Clase01.suma; Namespace Clase01
(assert
 (! ;; def=Clase01.fst(6,4-6,8); use=Clase01.fst(6,4-6,8)
  (forall ((@x0 Term) (@x1 Term))
   (! (implies
     (and (HasType @x0 Prims.int) (HasType @x1 Prims.int))
     (HasType (Clase01.suma @x0 @x1) Prims.int))
    :pattern ((Clase01.suma @x0 @x1))
    :qid typing_Clase01.suma))
  :named typing_Clase01.suma))
; refinement kinding
;;; Fact-ids: Name FStar.Pervasives.false_elim; Namespace FStar.Pervasives
(assert
 (! (HasType Tm_refine_f1ecc6ab6882a651504f328937700647 Tm_type)
  :named refinement_kinding_Tm_refine_f1ecc6ab6882a651504f328937700647))
; refinement kinding
;;; Fact-ids: Name Prims.pos; Namespace Prims
(assert
 (! (HasType Tm_refine_774ba3f728d91ead8ef40be66c9802e5 Tm_type)
  :named refinement_kinding_Tm_refine_774ba3f728d91ead8ef40be66c9802e5))
; refinement kinding
;;; Fact-ids: Name Prims.prop; Namespace Prims
(assert
 (! (HasType Tm_refine_73f210ca6e0061ed4a3150f69b8f33bf Tm_type)
  :named refinement_kinding_Tm_refine_73f210ca6e0061ed4a3150f69b8f33bf))
; refinement kinding
;;; Fact-ids: Name Prims.nat; Namespace Prims
(assert
 (! (HasType Tm_refine_542f9d4f129664613f2483a6c88bc7c2 Tm_type)
  :named refinement_kinding_Tm_refine_542f9d4f129664613f2483a6c88bc7c2))
; refinement kinding
;;; Fact-ids: Name Prims.eqtype; Namespace Prims
(assert
 (! (HasType Tm_refine_414d0a9f578ab0048252f8c8f552b99f Tm_type)
  :named refinement_kinding_Tm_refine_414d0a9f578ab0048252f8c8f552b99f))
; refinement kinding
;;; Fact-ids: Name Prims.nonzero; Namespace Prims
(assert
 (! (HasType Tm_refine_0766302b68bb44ab7aff8c4d8be0b46f Tm_type)
  :named refinement_kinding_Tm_refine_0766302b68bb44ab7aff8c4d8be0b46f))
; refinement_interpretation
;;; Fact-ids: Name FStar.Pervasives.false_elim; Namespace FStar.Pervasives
(assert
 (! ;; def=FStar.Pervasives.fsti(623,26-623,42); use=FStar.Pervasives.fsti(623,26-623,42)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (iff (HasTypeFuel @u0 @x1 Tm_refine_f1ecc6ab6882a651504f328937700647) false)
    :pattern ((HasTypeFuel @u0 @x1 Tm_refine_f1ecc6ab6882a651504f328937700647))
    :qid refinement_interpretation_Tm_refine_f1ecc6ab6882a651504f328937700647))
  :named refinement_interpretation_Tm_refine_f1ecc6ab6882a651504f328937700647))
; refinement_interpretation
;;; Fact-ids: Name Prims.pos; Namespace Prims
(assert
 (! ;; def=Prims.fst(685,11-685,24); use=Prims.fst(685,11-685,24)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 Tm_refine_774ba3f728d91ead8ef40be66c9802e5)
     (and
      (HasTypeFuel @u0 @x1 Prims.int)
      ;; def=Prims.fst(685,18-685,23); use=Prims.fst(685,18-685,23)
      (> (BoxInt_proj_0 @x1) (BoxInt_proj_0 (BoxInt 0)))))
    :pattern ((HasTypeFuel @u0 @x1 Tm_refine_774ba3f728d91ead8ef40be66c9802e5))
    :qid refinement_interpretation_Tm_refine_774ba3f728d91ead8ef40be66c9802e5))
  :named refinement_interpretation_Tm_refine_774ba3f728d91ead8ef40be66c9802e5))
; refinement_interpretation
;;; Fact-ids: Name Prims.prop; Namespace Prims
(assert
 (! ;; def=Prims.fst(312,12-312,41); use=Prims.fst(312,12-312,41)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 Tm_refine_73f210ca6e0061ed4a3150f69b8f33bf)
     (and
      (HasTypeFuel @u0 @x1 Tm_type)
      ;; def=Prims.fst(312,21-312,40); use=Prims.fst(312,21-312,40)
      (Valid
       ;; def=Prims.fst(312,21-312,40); use=Prims.fst(312,21-312,40)
       (Prims.subtype_of @x1 Prims.unit))))
    :pattern ((HasTypeFuel @u0 @x1 Tm_refine_73f210ca6e0061ed4a3150f69b8f33bf))
    :qid refinement_interpretation_Tm_refine_73f210ca6e0061ed4a3150f69b8f33bf))
  :named refinement_interpretation_Tm_refine_73f210ca6e0061ed4a3150f69b8f33bf))
; refinement_interpretation
;;; Fact-ids: Name Prims.nat; Namespace Prims
(assert
 (! ;; def=Prims.fst(682,11-682,25); use=Prims.fst(682,11-682,25)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 Tm_refine_542f9d4f129664613f2483a6c88bc7c2)
     (and
      (HasTypeFuel @u0 @x1 Prims.int)
      ;; def=Prims.fst(682,18-682,24); use=Prims.fst(682,18-682,24)
      (>= (BoxInt_proj_0 @x1) (BoxInt_proj_0 (BoxInt 0)))))
    :pattern ((HasTypeFuel @u0 @x1 Tm_refine_542f9d4f129664613f2483a6c88bc7c2))
    :qid refinement_interpretation_Tm_refine_542f9d4f129664613f2483a6c88bc7c2))
  :named refinement_interpretation_Tm_refine_542f9d4f129664613f2483a6c88bc7c2))
; refinement_interpretation
;;; Fact-ids: Name Prims.eqtype; Namespace Prims
(assert
 (! ;; def=Prims.fst(81,14-81,31); use=Prims.fst(81,14-81,31)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 Tm_refine_414d0a9f578ab0048252f8c8f552b99f)
     (and
      (HasTypeFuel @u0 @x1 Tm_type)
      ;; def=Prims.fst(81,23-81,30); use=Prims.fst(81,23-81,30)
      (Valid
       ;; def=Prims.fst(81,23-81,30); use=Prims.fst(81,23-81,30)
       (Prims.hasEq @x1))))
    :pattern ((HasTypeFuel @u0 @x1 Tm_refine_414d0a9f578ab0048252f8c8f552b99f))
    :qid refinement_interpretation_Tm_refine_414d0a9f578ab0048252f8c8f552b99f))
  :named refinement_interpretation_Tm_refine_414d0a9f578ab0048252f8c8f552b99f))
; refinement_interpretation
;;; Fact-ids: Name Prims.nonzero; Namespace Prims
(assert
 (! ;; def=Prims.fst(688,15-688,29); use=Prims.fst(688,15-688,29)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 Tm_refine_0766302b68bb44ab7aff8c4d8be0b46f)
     (and
      (HasTypeFuel @u0 @x1 Prims.int)
      ;; def=Prims.fst(688,22-688,28); use=Prims.fst(688,22-688,28)
      (not (= @x1 (BoxInt 0)))))
    :pattern ((HasTypeFuel @u0 @x1 Tm_refine_0766302b68bb44ab7aff8c4d8be0b46f))
    :qid refinement_interpretation_Tm_refine_0766302b68bb44ab7aff8c4d8be0b46f))
  :named refinement_interpretation_Tm_refine_0766302b68bb44ab7aff8c4d8be0b46f))
;;; Fact-ids: Name Prims.op_Addition; Namespace Prims
(assert
 (! ;; def=Prims.fst(560,4-560,15); use=Prims.fst(560,4-560,15)
  (forall ((@x0 Term) (@x1 Term))
   (! (= (Prims.op_Addition @x0 @x1) (BoxInt (+ (BoxInt_proj_0 @x0) (BoxInt_proj_0 @x1))))
    :pattern ((Prims.op_Addition @x0 @x1))
    :qid primitive_Prims.op_Addition))
  :named primitive_Prims.op_Addition))
; int typing
;;; Fact-ids: Name Prims.int; Namespace Prims
(assert
 (! (forall ((@u0 Int)) (! (HasType (BoxInt @u0) Prims.int) :pattern ((BoxInt @u0)) :qid int_typing))
  :named int_typing))
; int inversion
;;; Fact-ids: Name Prims.int; Namespace Prims
(assert
 (! (forall ((@u0 Fuel) (@x1 Term))
   (! (implies (HasTypeFuel @u0 @x1 Prims.int) (is-BoxInt @x1))
    :pattern ((HasTypeFuel @u0 @x1 Prims.int))
    :qid int_inversion))
  :named int_inversion))
; haseq for Tm_refine_f1ecc6ab6882a651504f328937700647
;;; Fact-ids: Name FStar.Pervasives.false_elim; Namespace FStar.Pervasives
(assert
 (! (iff
   (Valid (Prims.hasEq Tm_refine_f1ecc6ab6882a651504f328937700647))
   (Valid (Prims.hasEq Prims.unit)))
  :named haseqTm_refine_f1ecc6ab6882a651504f328937700647))
; haseq for Tm_refine_774ba3f728d91ead8ef40be66c9802e5
;;; Fact-ids: Name Prims.pos; Namespace Prims
(assert
 (! (iff
   (Valid (Prims.hasEq Tm_refine_774ba3f728d91ead8ef40be66c9802e5))
   (Valid (Prims.hasEq Prims.int)))
  :named haseqTm_refine_774ba3f728d91ead8ef40be66c9802e5))
; haseq for Tm_refine_73f210ca6e0061ed4a3150f69b8f33bf
;;; Fact-ids: Name Prims.prop; Namespace Prims
(assert
 (! (iff
   (Valid (Prims.hasEq Tm_refine_73f210ca6e0061ed4a3150f69b8f33bf))
   (Valid (Prims.hasEq Tm_type)))
  :named haseqTm_refine_73f210ca6e0061ed4a3150f69b8f33bf))
; haseq for Tm_refine_542f9d4f129664613f2483a6c88bc7c2
;;; Fact-ids: Name Prims.nat; Namespace Prims
(assert
 (! (iff
   (Valid (Prims.hasEq Tm_refine_542f9d4f129664613f2483a6c88bc7c2))
   (Valid (Prims.hasEq Prims.int)))
  :named haseqTm_refine_542f9d4f129664613f2483a6c88bc7c2))
; haseq for Tm_refine_414d0a9f578ab0048252f8c8f552b99f
;;; Fact-ids: Name Prims.eqtype; Namespace Prims
(assert
 (! (iff
   (Valid (Prims.hasEq Tm_refine_414d0a9f578ab0048252f8c8f552b99f))
   (Valid (Prims.hasEq Tm_type)))
  :named haseqTm_refine_414d0a9f578ab0048252f8c8f552b99f))
; haseq for Tm_refine_0766302b68bb44ab7aff8c4d8be0b46f
;;; Fact-ids: Name Prims.nonzero; Namespace Prims
(assert
 (! (iff
   (Valid (Prims.hasEq Tm_refine_0766302b68bb44ab7aff8c4d8be0b46f))
   (Valid (Prims.hasEq Prims.int)))
  :named haseqTm_refine_0766302b68bb44ab7aff8c4d8be0b46f))
; function token typing
;;; Fact-ids: Name Prims.unit; Namespace Prims
(assert
 (! (HasType Prims.unit Prims.eqtype) :named function_token_typing_Prims.unit))
; function token typing
;;; Fact-ids: Name Prims.nat; Namespace Prims
(assert
 (! (HasType Prims.nat Tm_type) :named function_token_typing_Prims.nat))
; function token typing
;;; Fact-ids: Name Prims.logical; Namespace Prims
(assert
 (! (HasType Prims.logical Tm_type) :named function_token_typing_Prims.logical))
; function token typing
;;; Fact-ids: Name Prims.int; Namespace Prims
(assert
 (! (HasType Prims.int Prims.eqtype) :named function_token_typing_Prims.int))
; function token typing
;;; Fact-ids: Name Prims.eqtype; Namespace Prims
(assert
 (! (HasType Prims.eqtype Tm_type) :named function_token_typing_Prims.eqtype))
; Equation for Prims.subtype_of
;;; Fact-ids: Name Prims.subtype_of; Namespace Prims
(assert
 (! ;; def=Prims.fst(299,4-299,14); use=Prims.fst(299,4-299,14)
  (forall ((@x0 Term) (@x1 Term))
   (! (=
     (Valid (Prims.subtype_of @x0 @x1))
     ;; def=Prims.fst(299,31-299,60); use=Prims.fst(299,31-299,60)
     (forall ((@x2 Term))
      (! (implies (HasType @x2 @x0) (HasType @x2 @x1)) :qid equation_Prims.subtype_of.1)))
    :pattern ((Prims.subtype_of @x0 @x1))
    :qid equation_Prims.subtype_of))
  :named equation_Prims.subtype_of))
; Equation for Prims.nat
;;; Fact-ids: Name Prims.nat; Namespace Prims
(assert
 (! (= Prims.nat Tm_refine_542f9d4f129664613f2483a6c88bc7c2) :named equation_Prims.nat))
; Equation for Prims.logical
;;; Fact-ids: Name Prims.logical; Namespace Prims
(assert
 (! (= Prims.logical Tm_type) :named equation_Prims.logical))
; Equation for Prims.eqtype
;;; Fact-ids: Name Prims.eqtype; Namespace Prims
(assert
 (! (= Prims.eqtype Tm_refine_414d0a9f578ab0048252f8c8f552b99f) :named equation_Prims.eqtype))
; Equation for Clase01.suma
;;; Fact-ids: Name Clase01.suma; Namespace Clase01
(assert
 (! ;; def=Clase01.fst(6,4-6,8); use=Clase01.fst(6,4-6,8)
  (forall ((@x0 Term) (@x1 Term))
   (! (= (Clase01.suma @x0 @x1) (Prims.op_Addition @x0 @x1))
    :pattern ((Clase01.suma @x0 @x1))
    :qid equation_Clase01.suma))
  :named equation_Clase01.suma))
; Prop-typing for Prims.subtype_of
;;; Fact-ids: Name Prims.subtype_of; Namespace Prims
(assert
 (! ;; def=Prims.fst(299,4-299,14); use=Prims.fst(299,4-299,14)
  (forall ((@x0 Term) (@x1 Term))
   (! (implies
     (and (HasType @x0 Tm_type) (HasType @x1 Tm_type))
     (Valid (Prims.subtype_of (Prims.subtype_of @x0 @x1) Prims.unit)))
    :pattern ((Prims.subtype_of (Prims.subtype_of @x0 @x1) Prims.unit))
    :qid defn_equation_Prims.subtype_of))
  :named defn_equation_Prims.subtype_of))
; Constructor distinct
;;; Fact-ids: Name Prims.unit; Namespace Prims
(assert
 (! (= 125 (Term_constr_id Prims.unit)) :named constructor_distinct_Prims.unit))
; Constructor distinct
;;; Fact-ids: Name Prims.int; Namespace Prims
(assert
 (! (= 303 (Term_constr_id Prims.int)) :named constructor_distinct_Prims.int))
; pretyping
;;; Fact-ids: Name Prims.unit; Namespace Prims
(assert
 (! ;; def=Prims.fst(104,5-104,9); use=Prims.fst(104,5-104,9)
  (forall ((@x0 Term) (@u1 Fuel))
   (! (implies (HasTypeFuel @u1 @x0 Prims.unit) (= Prims.unit (PreType @x0)))
    :pattern ((HasTypeFuel @u1 @x0 Prims.unit))
    :qid Prims_pretyping_f8666440faa91836cc5a13998af863fc))
  :named Prims_pretyping_f8666440faa91836cc5a13998af863fc))
; pretyping
;;; Fact-ids: Name Prims.int; Namespace Prims
(assert
 (! ;; def=Prims.fst(522,5-522,8); use=Prims.fst(522,5-522,8)
  (forall ((@x0 Term) (@u1 Fuel))
   (! (implies (HasTypeFuel @u1 @x0 Prims.int) (= Prims.int (PreType @x0)))
    :pattern ((HasTypeFuel @u1 @x0 Prims.int))
    :qid Prims_pretyping_ae567c2fb75be05905677af440075565))
  :named Prims_pretyping_ae567c2fb75be05905677af440075565))
(push) ;; push{2
; Starting query at Clase01.fst(9,31-9,39)
(declare-fun label_1 () Bool)
; Encoding query formula : forall (x: Prims.nat) (y: Prims.nat). (*  - Could not prove post-condition
; *) Clase01.suma x y >= 0
; Context: While encoding a query
; While typechecking the top-level declaration `let addnat`
(push) ;; push{0
; <fuel='2' ifuel='1'>
;;; Fact-ids: 
(assert (! (= MaxFuel (SFuel (SFuel ZFuel))) :named @MaxFuel_assumption))
;;; Fact-ids: 
(assert (! (= MaxIFuel (SFuel ZFuel)) :named @MaxIFuel_assumption))
; query
;;; Fact-ids: 
(assert
 (! (not
   (forall ((@x0 Term) (@x1 Term))
    (! (implies
      (and (HasType @x0 Prims.nat) (HasType @x1 Prims.nat))
      ;; def=Prims.fst(682,18-682,24); use=Clase01.fst(9,31-9,39)
      (or
       label_1
       ;; def=Prims.fst(682,18-682,24); use=Clase01.fst(9,31-9,39)
       (>= (BoxInt_proj_0 (Clase01.suma @x0 @x1)) (BoxInt_proj_0 (BoxInt 0)))))
     :qid @query)))
  :named @query))
(set-option :rlimit 2723280)
(echo "<initial_stats>")
(echo "<statistics>") (get-info :all-statistics) (echo "</statistics>")
(echo "</initial_stats>")
(echo "<result>")
(check-sat)
(echo "</result>")
(set-option :rlimit 0)
(echo "<reason-unknown>") (get-info :reason-unknown) (echo "</reason-unknown>")
(echo "<labels>")
(echo "label_1")
(eval label_1)
(echo "</labels>")
(echo "Done!")
(pop) ;; 0}pop

; QUERY ID: (Clase01.addnat, 1)
; STATUS: unsat
; Z3 invocation started by F*
; F* version: 2025.08.07~dev -- commit hash: unset
; Z3 version (according to F*): 4.8.5

(pop) ;; 2}pop
; encoding sigelt let addnat
; <Start encoding let addnat>
(declare-fun Clase01.addnat (Term Term) Term)
; x: Prims.nat -> y: Prims.nat -> Prims.nat
(declare-fun Tm_arrow_2bb228db8432d0cdc106cb64c22e55ba () Term)
(declare-fun Clase01.addnat@tok () Term)
; </end encoding let addnat>

; encoding sigelt let suma3
; <Start encoding let suma3>
(declare-fun Clase01.suma3 (Term Term Term) Term)
; x: Prims.int -> y: Prims.int -> z: Prims.int -> Prims.int
(declare-fun Tm_arrow_ddaab270e9fdf46f80b29f3d5d5fdd24 () Term)
(declare-fun Clase01.suma3@tok () Term)
; </end encoding let suma3>

; encoding sigelt let incr
; <Start encoding let incr>
(declare-fun Clase01.incr (Term) Term)

(declare-fun Clase01.incr@tok () Term)
; </end encoding let incr>

; encoding sigelt let incr'
; <Start encoding let incr'>
(declare-fun Clase01.incr_ (Term) Term)
; x: Prims.nat -> Prims.int
(declare-fun Tm_arrow_fc34ca66de2f262c06145b17fb7ed6cb () Term)
(declare-fun Clase01.incr_@tok () Term)
; </end encoding let incr'>

; encoding sigelt let incr''
; <Start encoding let incr''>
(declare-fun Clase01.incr__ (Term) Term)
; x: Prims.nat -> Prims.nat
(declare-fun Tm_arrow_b71b847c8a1dce9fbabbfc40fd470d89 () Term)
(declare-fun Clase01.incr__@tok () Term)
; </end encoding let incr''>

(push) ;; push{2
; Starting query at Clase01.fst(21,39-21,47)
(declare-fun label_1 () Bool)
; Encoding query formula : forall (x: Prims.nat). (*  - Could not prove post-condition
; *) Clase01.suma x 1 = x + 1
; Context: While encoding a query
; While typechecking the top-level declaration `let incr'''`
(push) ;; push{0
; <fuel='2' ifuel='1'>
;;; Fact-ids: 
(assert (! (= MaxFuel (SFuel (SFuel ZFuel))) :named @MaxFuel_assumption))
;;; Fact-ids: 
(assert (! (= MaxIFuel (SFuel ZFuel)) :named @MaxIFuel_assumption))
; query
;;; Fact-ids: 
(assert
 (! (not
   (forall ((@x0 Term))
    (! (implies
      (HasType @x0 Prims.nat)
      ;; def=Clase01.fst(21,28-21,35); use=Clase01.fst(21,39-21,47)
      (or
       label_1
       ;; def=Clase01.fst(21,28-21,35); use=Clase01.fst(21,39-21,47)
       (= (Clase01.suma @x0 (BoxInt 1)) (Prims.op_Addition @x0 (BoxInt 1)))))
     :qid @query)))
  :named @query))
(set-option :rlimit 2723280)
(echo "<initial_stats>")
(echo "<statistics>") (get-info :all-statistics) (echo "</statistics>")
(echo "</initial_stats>")
(echo "<result>")
(check-sat)
(echo "</result>")
(set-option :rlimit 0)
(echo "<reason-unknown>") (get-info :reason-unknown) (echo "</reason-unknown>")
(echo "<labels>")
(echo "label_1")
(eval label_1)
(echo "</labels>")
(echo "Done!")
(pop) ;; 0}pop

; QUERY ID: (Clase01.incr''', 1)
; STATUS: unsat
; Z3 invocation started by F*
; F* version: 2025.08.07~dev -- commit hash: unset
; Z3 version (according to F*): 4.8.5

(pop) ;; 2}pop
; encoding sigelt let incr'''
; <Start encoding let incr'''>
(declare-fun Clase01.incr___ (Term) Term)
(declare-fun Tm_refine_1c0a3cec866ea42686274915ee561bf7 (Term) Term)
; x: Prims.nat -> y: Prims.int{y = x + 1}
(declare-fun Tm_arrow_640df34fcbe77956f1224a06bb9f9910 () Term)
(declare-fun Clase01.incr___@tok () Term)

; </end encoding let incr'''>

; encoding sigelt let addnat'
; <Start encoding let addnat'>
(declare-fun Clase01.addnat_ (Term Term) Term)
; x: Prims.nat -> y: Prims.nat -> Prims.int
(declare-fun Tm_arrow_324ec1d2cb079acdcaa5dbfdf0459c05 () Term)
(declare-fun Clase01.addnat_@tok () Term)
; </end encoding let addnat'>

; encoding sigelt let debilitar1
; <Start encoding let debilitar1>

(declare-fun Clase01.debilitar1 (Term) Term)


; f: (_: Prims.int -> Prims.int) -> _: Prims.nat -> Prims.int
(declare-fun Tm_arrow_b240d6f6a7e0cd995802ad79c69fe373 () Term)
(declare-fun Clase01.debilitar1@tok () Term)


; </end encoding let debilitar1>

; encoding sigelt let debilitar2
; <Start encoding let debilitar2>

(declare-fun Clase01.debilitar2 (Term) Term)


; f: (_: Prims.nat -> Prims.nat) -> _: Prims.nat -> Prims.int
(declare-fun Tm_arrow_902a0369f78597b2afe14c3ebe917636 () Term)
(declare-fun Clase01.debilitar2@tok () Term)


; </end encoding let debilitar2>

; encoding sigelt let debilitar3
; <Start encoding let debilitar3>
; _: Prims.int -> Prims.nat
(declare-fun Tm_arrow_fe3049f77bcd4464558b0c47b7372400 () Term)
(declare-fun Clase01.debilitar3 (Term) Term)


; f: (_: Prims.int -> Prims.nat) -> _: Prims.nat -> Prims.int
(declare-fun Tm_arrow_e09c659081f0588b8c011b6af2db9b4a () Term)
(declare-fun Clase01.debilitar3@tok () Term)


; </end encoding let debilitar3>

; encoding sigelt let par
; <Start encoding let par>
(declare-fun Clase01.par (Term) Term)
; x: Prims.int -> Prims.bool
(declare-fun Tm_arrow_2b00b574e3c859da902fc1b8ce85c0f1 () Term)
(declare-fun Clase01.par@tok () Term)
; </end encoding let par>

; encoding sigelt let impar
; <Start encoding let impar>
(declare-fun Clase01.impar (Term) Term)

(declare-fun Clase01.impar@tok () Term)
; </end encoding let impar>

; free var typing
;;; Fact-ids: Name Prims.bool; Namespace Prims
(assert
 (! (HasType Prims.bool Prims.eqtype) :named typing_Prims.bool))
; free var typing
;;; Fact-ids: Name Clase01.par; Namespace Clase01
(assert
 (! ;; def=Clase01.fst(31,4-31,7); use=Clase01.fst(31,4-31,7)
  (forall ((@x0 Term))
   (! (implies (HasType @x0 Prims.int) (HasType (Clase01.par @x0) Prims.bool))
    :pattern ((Clase01.par @x0))
    :qid typing_Clase01.par))
  :named typing_Clase01.par))
; free var typing
;;; Fact-ids: Name Clase01.impar; Namespace Clase01
(assert
 (! ;; def=Clase01.fst(32,4-32,9); use=Clase01.fst(32,4-32,9)
  (forall ((@x0 Term))
   (! (implies (HasType @x0 Prims.int) (HasType (Clase01.impar @x0) Prims.bool))
    :pattern ((Clase01.impar @x0))
    :qid typing_Clase01.impar))
  :named typing_Clase01.impar))
;;; Fact-ids: Name Prims.op_Modulus; Namespace Prims
(assert
 (! ;; def=Prims.fst(699,4-699,14); use=Prims.fst(699,4-699,14)
  (forall ((@x0 Term) (@x1 Term))
   (! (implies
     (not (= (BoxInt_proj_0 @x1) 0))
     (= (Prims.op_Modulus @x0 @x1) (BoxInt (mod (BoxInt_proj_0 @x0) (BoxInt_proj_0 @x1)))))
    :pattern ((Prims.op_Modulus @x0 @x1))
    :qid primitive_Prims.op_Modulus))
  :named primitive_Prims.op_Modulus))
;;; Fact-ids: Name Prims.op_Equality; Namespace Prims
(assert
 (! ;; def=Prims.fst(596,4-596,15); use=Prims.fst(596,4-596,15)
  (forall ((@x0 Term) (@x1 Term) (@x2 Term))
   (! (= (Prims.op_Equality @x0 @x1 @x2) (BoxBool (= @x1 @x2)))
    :pattern ((Prims.op_Equality @x0 @x1 @x2))
    :qid primitive_Prims.op_Equality))
  :named primitive_Prims.op_Equality))
; function token typing
;;; Fact-ids: Name Prims.bool; Namespace Prims
(assert
 (! (HasType Prims.bool Prims.eqtype) :named function_token_typing_Prims.bool))
; Equation for Clase01.par
;;; Fact-ids: Name Clase01.par; Namespace Clase01
(assert
 (! ;; def=Clase01.fst(31,4-31,7); use=Clase01.fst(31,4-31,7)
  (forall ((@x0 Term))
   (! (=
     (Clase01.par @x0)
     (Prims.op_Equality Prims.int (Prims.op_Modulus @x0 (BoxInt 2)) (BoxInt 0)))
    :pattern ((Clase01.par @x0))
    :qid equation_Clase01.par))
  :named equation_Clase01.par))
; Equation for Clase01.impar
;;; Fact-ids: Name Clase01.impar; Namespace Clase01
(assert
 (! ;; def=Clase01.fst(32,4-32,9); use=Clase01.fst(32,4-32,9)
  (forall ((@x0 Term))
   (! (=
     (Clase01.impar @x0)
     (Prims.op_Equality Prims.int (Prims.op_Modulus @x0 (BoxInt 2)) (BoxInt 1)))
    :pattern ((Clase01.impar @x0))
    :qid equation_Clase01.impar))
  :named equation_Clase01.impar))
; Constructor distinct
;;; Fact-ids: Name Prims.bool; Namespace Prims
(assert
 (! (= 107 (Term_constr_id Prims.bool)) :named constructor_distinct_Prims.bool))
; bool typing
;;; Fact-ids: Name Prims.bool; Namespace Prims
(assert
 (! (forall ((@u0 Bool))
   (! (HasType (BoxBool @u0) Prims.bool) :pattern ((BoxBool @u0)) :qid bool_typing))
  :named bool_typing))
; bool inversion
;;; Fact-ids: Name Prims.bool; Namespace Prims
(assert
 (! (forall ((@u0 Fuel) (@x1 Term))
   (! (implies (HasTypeFuel @u0 @x1 Prims.bool) (is-BoxBool @x1))
    :pattern ((HasTypeFuel @u0 @x1 Prims.bool))
    :qid bool_inversion))
  :named bool_inversion))
; pretyping
;;; Fact-ids: Name Prims.bool; Namespace Prims
(assert
 (! ;; def=Prims.fst(88,5-88,9); use=Prims.fst(88,5-88,9)
  (forall ((@x0 Term) (@u1 Fuel))
   (! (implies (HasTypeFuel @u1 @x0 Prims.bool) (= Prims.bool (PreType @x0)))
    :pattern ((HasTypeFuel @u1 @x0 Prims.bool))
    :qid Prims_pretyping_f537159ed795b314b4e58c260361ae86))
  :named Prims_pretyping_f537159ed795b314b4e58c260361ae86))
(push) ;; push{2
; Starting query at Clase01.fst(36,49-36,52)
(declare-fun label_1 () Bool)
(declare-fun Tm_refine_d6e44fa3c671823d8798169b624d0127 () Term)
; refinement kinding
;;; Fact-ids: 
(assert
 (! (HasType Tm_refine_d6e44fa3c671823d8798169b624d0127 Tm_type)
  :named refinement_kinding_Tm_refine_d6e44fa3c671823d8798169b624d0127))
; refinement_interpretation
;;; Fact-ids: 
(assert
 (! ;; def=Clase01.fst(36,13-36,27); use=Clase01.fst(36,13-36,27)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 Tm_refine_d6e44fa3c671823d8798169b624d0127)
     (and
      (HasTypeFuel @u0 @x1 Prims.int)
      ;; def=Clase01.fst(36,20-36,25); use=Clase01.fst(36,20-36,25)
      (BoxBool_proj_0 (Clase01.par @x1))))
    :pattern ((HasTypeFuel @u0 @x1 Tm_refine_d6e44fa3c671823d8798169b624d0127))
    :qid refinement_interpretation_Tm_refine_d6e44fa3c671823d8798169b624d0127))
  :named refinement_interpretation_Tm_refine_d6e44fa3c671823d8798169b624d0127))
; haseq for Tm_refine_d6e44fa3c671823d8798169b624d0127
;;; Fact-ids: 
(assert
 (! (iff
   (Valid (Prims.hasEq Tm_refine_d6e44fa3c671823d8798169b624d0127))
   (Valid (Prims.hasEq Prims.int)))
  :named haseqTm_refine_d6e44fa3c671823d8798169b624d0127))
; Encoding query formula : forall (x: Prims.int{Clase01.par x}). (*  - Could not prove post-condition
; *) Clase01.impar (x + 1)
; Context: While encoding a query
; While typechecking the top-level declaration `let incr''''`
(push) ;; push{0
; <fuel='2' ifuel='1'>
;;; Fact-ids: 
(assert (! (= MaxFuel (SFuel (SFuel ZFuel))) :named @MaxFuel_assumption))
;;; Fact-ids: 
(assert (! (= MaxIFuel (SFuel ZFuel)) :named @MaxIFuel_assumption))
; query
;;; Fact-ids: 
(assert
 (! (not
   (forall ((@x0 Term))
    (! (implies
      (HasType @x0 Tm_refine_d6e44fa3c671823d8798169b624d0127)
      ;; def=Clase01.fst(36,37-36,44); use=Clase01.fst(36,49-36,52)
      (or
       label_1
       ;; def=Clase01.fst(36,37-36,44); use=Clase01.fst(36,49-36,52)
       (BoxBool_proj_0 (Clase01.impar (Prims.op_Addition @x0 (BoxInt 1))))))
     :qid @query)))
  :named @query))
(set-option :rlimit 2723280)
(echo "<initial_stats>")
(echo "<statistics>") (get-info :all-statistics) (echo "</statistics>")
(echo "</initial_stats>")
(echo "<result>")
(check-sat)
(echo "</result>")
(set-option :rlimit 0)
(echo "<reason-unknown>") (get-info :reason-unknown) (echo "</reason-unknown>")
(echo "<labels>")
(echo "label_1")
(eval label_1)
(echo "</labels>")
(echo "Done!")
(pop) ;; 0}pop

; QUERY ID: (Clase01.incr'''', 1)
; STATUS: unsat
; Z3 invocation started by F*
; F* version: 2025.08.07~dev -- commit hash: unset
; Z3 version (according to F*): 4.8.5

(pop) ;; 2}pop
; encoding sigelt let incr''''
; <Start encoding let incr''''>
(declare-fun Tm_refine_d6e44fa3c671823d8798169b624d0127 () Term)
(declare-fun Clase01.incr____ (Term) Term)

(declare-fun Tm_refine_8dfabb3133abaa0087a4fdf93d7e6419 () Term)
; x: Prims.int{par x} -> y: Prims.int{impar y}
(declare-fun Tm_arrow_f06780f990c6978a8df5f1c72aa2385f () Term)
(declare-fun Clase01.incr____@tok () Term)


; </end encoding let incr''''>

(push) ;; push{2
; expect_failure
; refinement kinding
;;; Fact-ids: Name Clase01.incr''''; Namespace Clase01
(assert
 (! (HasType Tm_refine_d6e44fa3c671823d8798169b624d0127 Tm_type)
  :named refinement_kinding_Tm_refine_d6e44fa3c671823d8798169b624d0127))
; refinement kinding
;;; Fact-ids: Name Clase01.incr''''; Namespace Clase01
(assert
 (! (HasType Tm_refine_8dfabb3133abaa0087a4fdf93d7e6419 Tm_type)
  :named refinement_kinding_Tm_refine_8dfabb3133abaa0087a4fdf93d7e6419))
; refinement_interpretation
;;; Fact-ids: Name Clase01.incr''''; Namespace Clase01
(assert
 (! ;; def=Clase01.fst(36,13-36,27); use=Clase01.fst(36,13-36,27)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 Tm_refine_d6e44fa3c671823d8798169b624d0127)
     (and
      (HasTypeFuel @u0 @x1 Prims.int)
      ;; def=Clase01.fst(36,20-36,25); use=Clase01.fst(36,20-36,25)
      (BoxBool_proj_0 (Clase01.par @x1))))
    :pattern ((HasTypeFuel @u0 @x1 Tm_refine_d6e44fa3c671823d8798169b624d0127))
    :qid refinement_interpretation_Tm_refine_d6e44fa3c671823d8798169b624d0127))
  :named refinement_interpretation_Tm_refine_d6e44fa3c671823d8798169b624d0127))
; refinement_interpretation
;;; Fact-ids: Name Clase01.incr''''; Namespace Clase01
(assert
 (! ;; def=Clase01.fst(36,30-36,46); use=Clase01.fst(36,30-36,46)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 Tm_refine_8dfabb3133abaa0087a4fdf93d7e6419)
     (and
      (HasTypeFuel @u0 @x1 Prims.int)
      ;; def=Clase01.fst(36,37-36,44); use=Clase01.fst(36,37-36,44)
      (BoxBool_proj_0 (Clase01.impar @x1))))
    :pattern ((HasTypeFuel @u0 @x1 Tm_refine_8dfabb3133abaa0087a4fdf93d7e6419))
    :qid refinement_interpretation_Tm_refine_8dfabb3133abaa0087a4fdf93d7e6419))
  :named refinement_interpretation_Tm_refine_8dfabb3133abaa0087a4fdf93d7e6419))
;;; Fact-ids: Name Prims.op_Multiply; Namespace Prims
(assert
 (! ;; def=Prims.fst(548,4-548,15); use=Prims.fst(548,4-548,15)
  (forall ((@x0 Term) (@x1 Term))
   (! (= (Prims.op_Multiply @x0 @x1) (BoxInt (* (BoxInt_proj_0 @x0) (BoxInt_proj_0 @x1))))
    :pattern ((Prims.op_Multiply @x0 @x1))
    :qid primitive_Prims.op_Multiply))
  :named primitive_Prims.op_Multiply))
;;; Fact-ids: Name Prims.op_Division; Namespace Prims
(assert
 (! ;; def=Prims.fst(705,4-705,15); use=Prims.fst(705,4-705,15)
  (forall ((@x0 Term) (@x1 Term))
   (! (implies
     (not (= (BoxInt_proj_0 @x1) 0))
     (= (Prims.op_Division @x0 @x1) (BoxInt (div (BoxInt_proj_0 @x0) (BoxInt_proj_0 @x1)))))
    :pattern ((Prims.op_Division @x0 @x1))
    :qid primitive_Prims.op_Division))
  :named primitive_Prims.op_Division))
; haseq for Tm_refine_d6e44fa3c671823d8798169b624d0127
;;; Fact-ids: Name Clase01.incr''''; Namespace Clase01
(assert
 (! (iff
   (Valid (Prims.hasEq Tm_refine_d6e44fa3c671823d8798169b624d0127))
   (Valid (Prims.hasEq Prims.int)))
  :named haseqTm_refine_d6e44fa3c671823d8798169b624d0127))
; haseq for Tm_refine_8dfabb3133abaa0087a4fdf93d7e6419
;;; Fact-ids: Name Clase01.incr''''; Namespace Clase01
(assert
 (! (iff
   (Valid (Prims.hasEq Tm_refine_8dfabb3133abaa0087a4fdf93d7e6419))
   (Valid (Prims.hasEq Prims.int)))
  :named haseqTm_refine_8dfabb3133abaa0087a4fdf93d7e6419))
(push) ;; push{3
; Starting query at Clase01.fst(44,57-44,68)
(declare-fun label_1 () Bool)

; Encoding query formula : forall (a: Prims.int) (b: Prims.int{b <> 0}). (*  - Could not prove post-condition
; *) a * b / b = a
; Context: While encoding a query
; While typechecking the top-level declaration `let muldiv`
; While typechecking the top-level declaration `[@@expect_failure] let muldiv`
(push) ;; push{0
; <fuel='2' ifuel='1'>
;;; Fact-ids: 
(assert (! (= MaxFuel (SFuel (SFuel ZFuel))) :named @MaxFuel_assumption))
;;; Fact-ids: 
(assert (! (= MaxIFuel (SFuel ZFuel)) :named @MaxIFuel_assumption))
; query
;;; Fact-ids: 
(assert
 (! (not
   (forall ((@x0 Term) (@x1 Term))
    (! (implies
      (and (HasType @x0 Prims.int) (HasType @x1 Tm_refine_0766302b68bb44ab7aff8c4d8be0b46f))
      ;; def=Clase01.fst(44,48-44,53); use=Clase01.fst(44,57-44,68)
      (or
       label_1
       ;; def=Clase01.fst(44,48-44,53); use=Clase01.fst(44,57-44,68)
       (= (Prims.op_Division (Prims.op_Multiply @x0 @x1) @x1) @x0)))
     :qid @query)))
  :named @query))
(set-option :rlimit 2723280)
(echo "<initial_stats>")
(echo "<statistics>") (get-info :all-statistics) (echo "</statistics>")
(echo "</initial_stats>")
(echo "<result>")
(check-sat)
(echo "</result>")
(set-option :rlimit 0)
(echo "<reason-unknown>") (get-info :reason-unknown) (echo "</reason-unknown>")
(echo "<labels>")
(echo "label_1")
(eval label_1)
(echo "</labels>")
(echo "Done!")
(pop) ;; 0}pop

; QUERY ID: (Clase01.muldiv, 1)
; STATUS: unknown because canceled
; Z3 invocation started by F*
; F* version: 2025.08.07~dev -- commit hash: unset
; Z3 version (according to F*): 4.8.5

(push) ;; push{0
; <fuel='2' ifuel='2'>
;;; Fact-ids: 
(assert (! (= MaxFuel (SFuel (SFuel ZFuel))) :named @MaxFuel_assumption))
;;; Fact-ids: 
(assert (! (= MaxIFuel (SFuel (SFuel ZFuel))) :named @MaxIFuel_assumption))
; query
;;; Fact-ids: 
(assert
 (! (not
   (forall ((@x0 Term) (@x1 Term))
    (! (implies
      (and (HasType @x0 Prims.int) (HasType @x1 Tm_refine_0766302b68bb44ab7aff8c4d8be0b46f))
      ;; def=Clase01.fst(44,48-44,53); use=Clase01.fst(44,57-44,68)
      (or
       label_1
       ;; def=Clase01.fst(44,48-44,53); use=Clase01.fst(44,57-44,68)
       (= (Prims.op_Division (Prims.op_Multiply @x0 @x1) @x1) @x0)))
     :qid @query)))
  :named @query))
(set-option :rlimit 2723280)
(echo "<initial_stats>")
(echo "<statistics>") (get-info :all-statistics) (echo "</statistics>")
(echo "</initial_stats>")
(echo "<result>")
(check-sat)
(echo "</result>")
(set-option :rlimit 0)
(echo "<reason-unknown>") (get-info :reason-unknown) (echo "</reason-unknown>")
(echo "<labels>")
(echo "label_1")
(eval label_1)
(echo "</labels>")
(echo "Done!")
(pop) ;; 0}pop

; QUERY ID: (Clase01.muldiv, 1)
; STATUS: unknown because canceled
; Z3 invocation started by F*
; F* version: 2025.08.07~dev -- commit hash: unset
; Z3 version (according to F*): 4.8.5

(push) ;; push{0
; <fuel='4' ifuel='2'>
;;; Fact-ids: 
(assert
 (! (= MaxFuel (SFuel (SFuel (SFuel (SFuel ZFuel))))) :named @MaxFuel_assumption))
;;; Fact-ids: 
(assert (! (= MaxIFuel (SFuel (SFuel ZFuel))) :named @MaxIFuel_assumption))
; query
;;; Fact-ids: 
(assert
 (! (not
   (forall ((@x0 Term) (@x1 Term))
    (! (implies
      (and (HasType @x0 Prims.int) (HasType @x1 Tm_refine_0766302b68bb44ab7aff8c4d8be0b46f))
      ;; def=Clase01.fst(44,48-44,53); use=Clase01.fst(44,57-44,68)
      (or
       label_1
       ;; def=Clase01.fst(44,48-44,53); use=Clase01.fst(44,57-44,68)
       (= (Prims.op_Division (Prims.op_Multiply @x0 @x1) @x1) @x0)))
     :qid @query)))
  :named @query))
(set-option :rlimit 2723280)
(echo "<initial_stats>")
(echo "<statistics>") (get-info :all-statistics) (echo "</statistics>")
(echo "</initial_stats>")
(echo "<result>")
(check-sat)
(echo "</result>")
(set-option :rlimit 0)
(echo "<reason-unknown>") (get-info :reason-unknown) (echo "</reason-unknown>")
(echo "<labels>")
(echo "label_1")
(eval label_1)
(echo "</labels>")
(echo "Done!")
(pop) ;; 0}pop

; QUERY ID: (Clase01.muldiv, 1)
; STATUS: unknown because canceled
; Z3 invocation started by F*
; F* version: 2025.08.07~dev -- commit hash: unset
; Z3 version (according to F*): 4.8.5

(push) ;; push{0
; <fuel='8' ifuel='2'>
;;; Fact-ids: 
(assert
 (! (= MaxFuel (SFuel (SFuel (SFuel (SFuel (SFuel (SFuel (SFuel (SFuel ZFuel)))))))))
  :named @MaxFuel_assumption))
;;; Fact-ids: 
(assert (! (= MaxIFuel (SFuel (SFuel ZFuel))) :named @MaxIFuel_assumption))
; query
;;; Fact-ids: 
(assert
 (! (not
   (forall ((@x0 Term) (@x1 Term))
    (! (implies
      (and (HasType @x0 Prims.int) (HasType @x1 Tm_refine_0766302b68bb44ab7aff8c4d8be0b46f))
      ;; def=Clase01.fst(44,48-44,53); use=Clase01.fst(44,57-44,68)
      (or
       label_1
       ;; def=Clase01.fst(44,48-44,53); use=Clase01.fst(44,57-44,68)
       (= (Prims.op_Division (Prims.op_Multiply @x0 @x1) @x1) @x0)))
     :qid @query)))
  :named @query))
(set-option :rlimit 2723280)
(echo "<initial_stats>")
(echo "<statistics>") (get-info :all-statistics) (echo "</statistics>")
(echo "</initial_stats>")
(echo "<result>")
(check-sat)
(echo "</result>")
(set-option :rlimit 0)
(echo "<reason-unknown>") (get-info :reason-unknown) (echo "</reason-unknown>")
(echo "<labels>")
(echo "label_1")
(eval label_1)
(echo "</labels>")
(echo "Done!")
(pop) ;; 0}pop

; QUERY ID: (Clase01.muldiv, 1)
; STATUS: unknown because canceled
; Z3 invocation started by F*
; F* version: 2025.08.07~dev -- commit hash: unset
; Z3 version (according to F*): 4.8.5

(pop) ;; 3}pop
(pop) ;; 2}pop
; typing for data constructor proxy
;;; Fact-ids: Name Prims.trivial; Namespace Prims; Name Prims.T; Namespace Prims
(assert
 (! (HasType Prims.T@tok Prims.trivial) :named typing_tok_Prims.T@tok))
; free var typing
;;; Fact-ids: Name Prims.squash; Namespace Prims
(assert
 (! ;; def=Prims.fst(125,5-125,11); use=Prims.fst(125,5-125,11)
  (forall ((@x0 Term))
   (! (implies (HasType @x0 Tm_type) (HasType (Prims.squash @x0) Tm_type))
    :pattern ((Prims.squash @x0))
    :qid typing_Prims.squash))
  :named typing_Prims.squash))
; free var typing
;;; Fact-ids: Name Prims.pure_post'; Namespace Prims
(assert
 (! ;; def=Prims.fst(323,4-323,14); use=Prims.fst(323,4-323,14)
  (forall ((@x0 Term) (@x1 Term))
   (! (implies
     (and (HasType @x0 Tm_type) (HasType @x1 Tm_type))
     (HasType (Prims.pure_post_ @x0 @x1) Tm_type))
    :pattern ((Prims.pure_post_ @x0 @x1))
    :qid typing_Prims.pure_post_))
  :named typing_Prims.pure_post_))
; free var typing
;;; Fact-ids: Name Prims.pure_post; Namespace Prims
(assert
 (! ;; def=Prims.fst(324,4-324,13); use=Prims.fst(324,4-324,13)
  (forall ((@x0 Term))
   (! (implies (HasType @x0 Tm_type) (HasType (Prims.pure_post @x0) Tm_type))
    :pattern ((Prims.pure_post @x0))
    :qid typing_Prims.pure_post))
  :named typing_Prims.pure_post))
; free var typing
;;; Fact-ids: Name Prims.l_True; Namespace Prims
(assert
 (! (HasType Prims.l_True Prims.logical) :named typing_Prims.l_True))
; free var typing
;;; Fact-ids: Name Prims.guard_free; Namespace Prims
(assert
 (! ;; def=Prims.fst(354,5-354,15); use=Prims.fst(354,5-354,15)
  (forall ((@x0 Term))
   (! (implies (HasType @x0 Tm_type) (HasType (Prims.guard_free @x0) Tm_type))
    :pattern ((Prims.guard_free @x0))
    :qid typing_Prims.guard_free))
  :named typing_Prims.guard_free))
; True interpretation
;;; Fact-ids: Name Prims.l_True; Namespace Prims
(assert (! (Valid Prims.l_True) :named true_interp))
; refinement kinding
;;; Fact-ids: Name Clase01.incr''''; Namespace Clase01
(assert
 (! (HasType Tm_refine_d6e44fa3c671823d8798169b624d0127 Tm_type)
  :named refinement_kinding_Tm_refine_d6e44fa3c671823d8798169b624d0127))
; refinement kinding
;;; Fact-ids: Name Clase01.incr''''; Namespace Clase01
(assert
 (! (HasType Tm_refine_8dfabb3133abaa0087a4fdf93d7e6419 Tm_type)
  :named refinement_kinding_Tm_refine_8dfabb3133abaa0087a4fdf93d7e6419))
; refinement kinding
;;; Fact-ids: Name Prims.pure_post'; Namespace Prims
(assert
 (! ;; def=Prims.fst(323,31-323,40); use=Prims.fst(323,31-323,40)
  (forall ((@x0 Term) (@x1 Term))
   (! (HasType (Tm_refine_8d65e998a07dd53ec478e27017d9dba5 @x0 @x1) Tm_type)
    :pattern ((HasType (Tm_refine_8d65e998a07dd53ec478e27017d9dba5 @x0 @x1) Tm_type))
    :qid refinement_kinding_Tm_refine_8d65e998a07dd53ec478e27017d9dba5))
  :named refinement_kinding_Tm_refine_8d65e998a07dd53ec478e27017d9dba5))
; refinement kinding
;;; Fact-ids: Name Prims.squash; Namespace Prims
(assert
 (! ;; def=Prims.fst(125,32-125,42); use=Prims.fst(125,32-125,42)
  (forall ((@x0 Term))
   (! (HasType (Tm_refine_2de20c066034c13bf76e9c0b94f4806c @x0) Tm_type)
    :pattern ((HasType (Tm_refine_2de20c066034c13bf76e9c0b94f4806c @x0) Tm_type))
    :qid refinement_kinding_Tm_refine_2de20c066034c13bf76e9c0b94f4806c))
  :named refinement_kinding_Tm_refine_2de20c066034c13bf76e9c0b94f4806c))
; refinement_interpretation
;;; Fact-ids: Name Clase01.incr''''; Namespace Clase01
(assert
 (! ;; def=Clase01.fst(36,13-36,27); use=Clase01.fst(36,13-36,27)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 Tm_refine_d6e44fa3c671823d8798169b624d0127)
     (and
      (HasTypeFuel @u0 @x1 Prims.int)
      ;; def=Clase01.fst(36,20-36,25); use=Clase01.fst(36,20-36,25)
      (BoxBool_proj_0 (Clase01.par @x1))))
    :pattern ((HasTypeFuel @u0 @x1 Tm_refine_d6e44fa3c671823d8798169b624d0127))
    :qid refinement_interpretation_Tm_refine_d6e44fa3c671823d8798169b624d0127))
  :named refinement_interpretation_Tm_refine_d6e44fa3c671823d8798169b624d0127))
; refinement_interpretation
;;; Fact-ids: Name Clase01.incr''''; Namespace Clase01
(assert
 (! ;; def=Clase01.fst(36,30-36,46); use=Clase01.fst(36,30-36,46)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 Tm_refine_8dfabb3133abaa0087a4fdf93d7e6419)
     (and
      (HasTypeFuel @u0 @x1 Prims.int)
      ;; def=Clase01.fst(36,37-36,44); use=Clase01.fst(36,37-36,44)
      (BoxBool_proj_0 (Clase01.impar @x1))))
    :pattern ((HasTypeFuel @u0 @x1 Tm_refine_8dfabb3133abaa0087a4fdf93d7e6419))
    :qid refinement_interpretation_Tm_refine_8dfabb3133abaa0087a4fdf93d7e6419))
  :named refinement_interpretation_Tm_refine_8dfabb3133abaa0087a4fdf93d7e6419))
; refinement_interpretation
;;; Fact-ids: Name Prims.pure_post'; Namespace Prims
(assert
 (! ;; def=Prims.fst(323,31-323,40); use=Prims.fst(323,31-323,40)
  (forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 (Tm_refine_8d65e998a07dd53ec478e27017d9dba5 @x2 @x3))
     (and
      (HasTypeFuel @u0 @x1 @x2)
      ;; def=Prims.fst(323,18-323,21); use=Prims.fst(323,36-323,39)
      (Valid
       ;; def=Prims.fst(323,18-323,21); use=Prims.fst(323,36-323,39)
       @x3)))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_8d65e998a07dd53ec478e27017d9dba5 @x2 @x3)))
    :qid refinement_interpretation_Tm_refine_8d65e998a07dd53ec478e27017d9dba5))
  :named refinement_interpretation_Tm_refine_8d65e998a07dd53ec478e27017d9dba5))
; refinement_interpretation
;;; Fact-ids: Name Prims.squash; Namespace Prims
(assert
 (! ;; def=Prims.fst(125,32-125,42); use=Prims.fst(125,32-125,42)
  (forall ((@u0 Fuel) (@x1 Term) (@x2 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 (Tm_refine_2de20c066034c13bf76e9c0b94f4806c @x2))
     (and
      (HasTypeFuel @u0 @x1 Prims.unit)
      ;; def=Prims.fst(125,13-125,14); use=Prims.fst(125,40-125,41)
      (Valid
       ;; def=Prims.fst(125,13-125,14); use=Prims.fst(125,40-125,41)
       @x2)))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_2de20c066034c13bf76e9c0b94f4806c @x2)))
    :qid refinement_interpretation_Tm_refine_2de20c066034c13bf76e9c0b94f4806c))
  :named refinement_interpretation_Tm_refine_2de20c066034c13bf76e9c0b94f4806c))
;;; Fact-ids: Name Prims.op_Minus; Namespace Prims
(assert
 (! ;; def=Prims.fst(566,4-566,12); use=Prims.fst(566,4-566,12)
  (forall ((@x0 Term))
   (! (= (Prims.op_Minus @x0) (BoxInt (- (BoxInt_proj_0 @x0))))
    :pattern ((Prims.op_Minus @x0))
    :qid primitive_Prims.op_Minus))
  :named primitive_Prims.op_Minus))
;;; Fact-ids: Name Prims.op_GreaterThanOrEqual; Namespace Prims
(assert
 (! ;; def=Prims.fst(584,4-584,25); use=Prims.fst(584,4-584,25)
  (forall ((@x0 Term) (@x1 Term))
   (! (=
     (Prims.op_GreaterThanOrEqual @x0 @x1)
     (BoxBool (>= (BoxInt_proj_0 @x0) (BoxInt_proj_0 @x1))))
    :pattern ((Prims.op_GreaterThanOrEqual @x0 @x1))
    :qid primitive_Prims.op_GreaterThanOrEqual))
  :named primitive_Prims.op_GreaterThanOrEqual))
; kinding_Tm_arrow_92458cff82f9ffee1f6e26a1c0c579f3
;;; Fact-ids: Name Prims.pure_post'; Namespace Prims
(assert
 (! ;; def=Prims.fst(323,31-323,54); use=Prims.fst(323,31-323,54)
  (forall ((@x0 Term) (@x1 Term))
   (! (HasType (Tm_arrow_92458cff82f9ffee1f6e26a1c0c579f3 @x0 @x1) Tm_type)
    :pattern ((HasType (Tm_arrow_92458cff82f9ffee1f6e26a1c0c579f3 @x0 @x1) Tm_type))
    :qid kinding_Tm_arrow_92458cff82f9ffee1f6e26a1c0c579f3))
  :named kinding_Tm_arrow_92458cff82f9ffee1f6e26a1c0c579f3))
;;; Fact-ids: Name Prims.trivial; Namespace Prims; Name Prims.T; Namespace Prims
(assert
 (! (HasType Prims.trivial Tm_type) :named kinding_Prims.trivial@tok))
; haseq for Tm_refine_d6e44fa3c671823d8798169b624d0127
;;; Fact-ids: Name Clase01.incr''''; Namespace Clase01
(assert
 (! (iff
   (Valid (Prims.hasEq Tm_refine_d6e44fa3c671823d8798169b624d0127))
   (Valid (Prims.hasEq Prims.int)))
  :named haseqTm_refine_d6e44fa3c671823d8798169b624d0127))
; haseq for Tm_refine_8dfabb3133abaa0087a4fdf93d7e6419
;;; Fact-ids: Name Clase01.incr''''; Namespace Clase01
(assert
 (! (iff
   (Valid (Prims.hasEq Tm_refine_8dfabb3133abaa0087a4fdf93d7e6419))
   (Valid (Prims.hasEq Prims.int)))
  :named haseqTm_refine_8dfabb3133abaa0087a4fdf93d7e6419))
; haseq for Tm_refine_8d65e998a07dd53ec478e27017d9dba5
;;; Fact-ids: Name Prims.pure_post'; Namespace Prims
(assert
 (! ;; def=Prims.fst(323,31-323,40); use=Prims.fst(323,31-323,40)
  (forall ((@x0 Term) (@x1 Term))
   (! (iff
     (Valid (Prims.hasEq (Tm_refine_8d65e998a07dd53ec478e27017d9dba5 @x0 @x1)))
     (Valid (Prims.hasEq @x0)))
    :pattern ((Valid (Prims.hasEq (Tm_refine_8d65e998a07dd53ec478e27017d9dba5 @x0 @x1))))
    :qid haseqTm_refine_8d65e998a07dd53ec478e27017d9dba5))
  :named haseqTm_refine_8d65e998a07dd53ec478e27017d9dba5))
; haseq for Tm_refine_2de20c066034c13bf76e9c0b94f4806c
;;; Fact-ids: Name Prims.squash; Namespace Prims
(assert
 (! ;; def=Prims.fst(125,32-125,42); use=Prims.fst(125,32-125,42)
  (forall ((@x0 Term))
   (! (iff
     (Valid (Prims.hasEq (Tm_refine_2de20c066034c13bf76e9c0b94f4806c @x0)))
     (Valid (Prims.hasEq Prims.unit)))
    :pattern ((Valid (Prims.hasEq (Tm_refine_2de20c066034c13bf76e9c0b94f4806c @x0))))
    :qid haseqTm_refine_2de20c066034c13bf76e9c0b94f4806c))
  :named haseqTm_refine_2de20c066034c13bf76e9c0b94f4806c))
; function token typing
;;; Fact-ids: Name Prims.l_True; Namespace Prims
(assert
 (! (HasType Prims.l_True Prims.logical) :named function_token_typing_Prims.l_True))
; inversion axiom
;;; Fact-ids: Name Prims.trivial; Namespace Prims; Name Prims.T; Namespace Prims
(assert
 (! ;; def=Prims.fst(99,5-99,12); use=Prims.fst(99,5-99,12)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (implies (HasTypeFuel @u0 @x1 Prims.trivial) (is-Prims.T @x1))
    :pattern ((HasTypeFuel @u0 @x1 Prims.trivial))
    :qid fuel_guarded_inversion_Prims.trivial))
  :named fuel_guarded_inversion_Prims.trivial))
; Equation for Prims.squash
;;; Fact-ids: Name Prims.squash; Namespace Prims
(assert
 (! ;; def=Prims.fst(125,5-125,11); use=Prims.fst(125,5-125,11)
  (forall ((@x0 Term))
   (! (= (Prims.squash @x0) (Tm_refine_2de20c066034c13bf76e9c0b94f4806c @x0))
    :pattern ((Prims.squash @x0))
    :qid equation_Prims.squash))
  :named equation_Prims.squash))
; Equation for Prims.pure_post'
;;; Fact-ids: Name Prims.pure_post'; Namespace Prims
(assert
 (! ;; def=Prims.fst(323,4-323,14); use=Prims.fst(323,4-323,14)
  (forall ((@x0 Term) (@x1 Term))
   (! (= (Prims.pure_post_ @x0 @x1) (Tm_arrow_92458cff82f9ffee1f6e26a1c0c579f3 @x1 @x0))
    :pattern ((Prims.pure_post_ @x0 @x1))
    :qid equation_Prims.pure_post_))
  :named equation_Prims.pure_post_))
; Equation for Prims.pure_post
;;; Fact-ids: Name Prims.pure_post; Namespace Prims
(assert
 (! ;; def=Prims.fst(324,4-324,13); use=Prims.fst(324,4-324,13)
  (forall ((@x0 Term))
   (! (= (Prims.pure_post @x0) (Prims.pure_post_ @x0 Prims.l_True))
    :pattern ((Prims.pure_post @x0))
    :qid equation_Prims.pure_post))
  :named equation_Prims.pure_post))
; Equation for Prims.l_True
;;; Fact-ids: Name Prims.l_True; Namespace Prims
(assert
 (! (= Prims.l_True (Prims.squash Prims.trivial)) :named equation_Prims.l_True))
; equality for proxy
;;; Fact-ids: Name Prims.trivial; Namespace Prims; Name Prims.T; Namespace Prims
(assert
 (! (= Prims.T@tok Prims.T) :named equality_tok_Prims.T@tok))
; data constructor typing intro
;;; Fact-ids: Name Prims.trivial; Namespace Prims; Name Prims.T; Namespace Prims
(assert
 (! ;; def=Prims.fst(99,17-99,18); use=Prims.fst(99,17-99,18)
  (forall ((@u0 Fuel))
   (! (HasTypeFuel @u0 Prims.T Prims.trivial)
    :pattern ((HasTypeFuel @u0 Prims.T Prims.trivial))
    :qid data_typing_intro_Prims.T@tok))
  :named data_typing_intro_Prims.T@tok))
; Constructor distinct
;;; Fact-ids: Name Prims.trivial; Namespace Prims; Name Prims.T; Namespace Prims
(assert
 (! (= 116 (Term_constr_id Prims.trivial)) :named constructor_distinct_Prims.trivial))
; Constructor distinct
;;; Fact-ids: Name Prims.trivial; Namespace Prims; Name Prims.T; Namespace Prims
(assert
 (! (= 122 (Term_constr_id Prims.T)) :named constructor_distinct_Prims.T))
; pretyping
;;; Fact-ids: Name Prims.trivial; Namespace Prims; Name Prims.T; Namespace Prims
(assert
 (! ;; def=Prims.fst(99,5-99,12); use=Prims.fst(99,5-99,12)
  (forall ((@x0 Term) (@u1 Fuel))
   (! (implies (HasTypeFuel @u1 @x0 Prims.trivial) (= Prims.trivial (PreType @x0)))
    :pattern ((HasTypeFuel @u1 @x0 Prims.trivial))
    :qid Prims_pretyping_e8ffb7d227a1bbf69407a8d2ad2c4c83))
  :named Prims_pretyping_e8ffb7d227a1bbf69407a8d2ad2c4c83))
; pre-typing for functions
;;; Fact-ids: Name Prims.pure_post'; Namespace Prims
(assert
 (! ;; def=Prims.fst(323,31-323,54); use=Prims.fst(323,31-323,54)
  (forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (implies
     (HasTypeFuel @u0 @x1 (Tm_arrow_92458cff82f9ffee1f6e26a1c0c579f3 @x2 @x3))
     (is-Tm_arrow (PreType @x1)))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_arrow_92458cff82f9ffee1f6e26a1c0c579f3 @x2 @x3)))
    :qid Prims_pre_typing_Tm_arrow_92458cff82f9ffee1f6e26a1c0c579f3))
  :named Prims_pre_typing_Tm_arrow_92458cff82f9ffee1f6e26a1c0c579f3))
; interpretation_Tm_arrow_92458cff82f9ffee1f6e26a1c0c579f3
;;; Fact-ids: Name Prims.pure_post'; Namespace Prims
(assert
 (! ;; def=Prims.fst(323,31-323,54); use=Prims.fst(323,31-323,54)
  (forall ((@x0 Term) (@x1 Term) (@x2 Term))
   (! (iff
     (HasTypeZ @x0 (Tm_arrow_92458cff82f9ffee1f6e26a1c0c579f3 @x1 @x2))
     (and
      ;; def=Prims.fst(323,31-323,54); use=Prims.fst(323,31-323,54)
      (forall ((@x3 Term))
       (! (implies
         (HasType @x3 (Tm_refine_8d65e998a07dd53ec478e27017d9dba5 @x2 @x1))
         (HasType (ApplyTT @x0 @x3) Tm_type))
        :pattern ((ApplyTT @x0 @x3))
        :qid Prims_interpretation_Tm_arrow_92458cff82f9ffee1f6e26a1c0c579f3.1))
      (IsTotFun @x0)))
    :pattern ((HasTypeZ @x0 (Tm_arrow_92458cff82f9ffee1f6e26a1c0c579f3 @x1 @x2)))
    :qid Prims_interpretation_Tm_arrow_92458cff82f9ffee1f6e26a1c0c579f3))
  :named Prims_interpretation_Tm_arrow_92458cff82f9ffee1f6e26a1c0c579f3))
(push) ;; push{2
; Starting query at Clase01.fst(47,24-47,48)
(declare-fun label_2 () Bool)
(declare-fun label_1 () Bool)
; Encoding query formula : forall (x: Prims.int).
;   (*  - Could not prove post-condition
; *)
;   forall (k: Prims.pure_post Prims.nat).
;     (forall (x: Prims.nat). {:pattern Prims.guard_free (k x)} Prims.auto_squash (k x)) ==>
;     (x >= 0 == true ==> x >= 0) /\
;     (~(x >= 0 = true) ==> (forall (b: Prims.bool). x >= 0 == b ==> - x >= 0))
; Context: While encoding a query
; While typechecking the top-level declaration `let abs`
(push) ;; push{0
; <fuel='2' ifuel='1'>
;;; Fact-ids: 
(assert (! (= MaxFuel (SFuel (SFuel ZFuel))) :named @MaxFuel_assumption))
;;; Fact-ids: 
(assert (! (= MaxIFuel (SFuel ZFuel)) :named @MaxIFuel_assumption))
; query
;;; Fact-ids: 
(assert
 (! (not
   (forall ((@x0 Term))
    (! (implies
      (HasType @x0 Prims.int)
      (forall ((@x1 Term))
       (! (implies
         (and
          (HasType @x1 (Prims.pure_post Prims.nat))
          ;; def=Prims.fst(410,27-410,88); use=Clase01.fst(47,24-47,48)
          (forall ((@x2 Term))
           (! ;; def=Prims.fst(410,84-410,87); use=Clase01.fst(47,24-47,48)
            (Valid
             ;; def=Prims.fst(410,84-410,87); use=Clase01.fst(47,24-47,48)
             (ApplyTT @x1 @x2))
            :pattern ((ApplyTT @x1 @x2))
            :qid @query.2)))
         ;; def=Prims.fst(397,2-397,39); use=Clase01.fst(47,24-47,48)
         (and
          (implies
           ;; def=Clase01.fst(47,27-47,33); use=Clase01.fst(47,27-47,33)
           (= (Prims.op_GreaterThanOrEqual @x0 (BoxInt 0)) (BoxBool true))
           ;; def=Prims.fst(682,18-682,24); use=Clase01.fst(47,39-47,40)
           (or
            label_1
            ;; def=Prims.fst(682,18-682,24); use=Clase01.fst(47,39-47,40)
            (>= (BoxInt_proj_0 @x0) (BoxInt_proj_0 (BoxInt 0)))))
          (implies
           ;; def=Prims.fst(397,19-397,21); use=Clase01.fst(47,24-47,48)
           (not
            ;; def=Clase01.fst(47,27-47,33); use=Clase01.fst(47,27-47,33)
            (= (Prims.op_GreaterThanOrEqual @x0 (BoxInt 0)) (BoxBool true)))
           ;; def=Prims.fst(421,99-421,120); use=Clase01.fst(47,24-47,48)
           (forall ((@x2 Term))
            (! (implies
              (and
               (HasType @x2 Prims.bool)
               ;; def=Clase01.fst(47,27-47,48); use=Clase01.fst(47,27-47,48)
               (= (Prims.op_GreaterThanOrEqual @x0 (BoxInt 0)) @x2))
              ;; def=Prims.fst(682,18-682,24); use=Clase01.fst(47,46-47,48)
              (or
               label_2
               ;; def=Prims.fst(682,18-682,24); use=Clase01.fst(47,46-47,48)
               (>= (BoxInt_proj_0 (Prims.op_Minus @x0)) (BoxInt_proj_0 (BoxInt 0)))))
             :qid @query.3)))))
        :qid @query.1)))
     :qid @query)))
  :named @query))
(set-option :rlimit 2723280)
(echo "<initial_stats>")
(echo "<statistics>") (get-info :all-statistics) (echo "</statistics>")
(echo "</initial_stats>")
(echo "<result>")
(check-sat)
(echo "</result>")
(set-option :rlimit 0)
(echo "<reason-unknown>") (get-info :reason-unknown) (echo "</reason-unknown>")
(echo "<labels>")
(echo "label_2")
(eval label_2)
(echo "label_1")
(eval label_1)
(echo "</labels>")
(echo "Done!")
(pop) ;; 0}pop

; QUERY ID: (Clase01.abs, 1)
; STATUS: unsat
; Z3 invocation started by F*
; F* version: 2025.08.07~dev -- commit hash: unset
; Z3 version (according to F*): 4.8.5

(pop) ;; 2}pop
; encoding sigelt let abs
; <Start encoding let abs>
(declare-fun Clase01.abs (Term) Term)

(declare-fun Clase01.abs@tok () Term)
; </end encoding let abs>

;;; Fact-ids: Name Prims.op_BarBar; Namespace Prims
(assert
 (! ;; def=Prims.fst(536,4-536,13); use=Prims.fst(536,4-536,13)
  (forall ((@x0 Term) (@x1 Term))
   (! (= (Prims.op_BarBar @x0 @x1) (BoxBool (or (BoxBool_proj_0 @x0) (BoxBool_proj_0 @x1))))
    :pattern ((Prims.op_BarBar @x0 @x1))
    :qid primitive_Prims.op_BarBar))
  :named primitive_Prims.op_BarBar))
(push) ;; push{2
; Starting query at Clase01.fst(50,64-50,87)
(declare-fun label_3 () Bool)
(declare-fun label_2 () Bool)
(declare-fun label_1 () Bool)
(declare-fun Tm_refine_4763580b8f6d91acfdd99ce186d05f87 (Term Term) Term)
; refinement kinding
;;; Fact-ids: 
(assert
 (! ;; def=Clase01.fst(50,22-50,61); use=Clase01.fst(50,64-50,87)
  (forall ((@x0 Term) (@x1 Term))
   (! (HasType (Tm_refine_4763580b8f6d91acfdd99ce186d05f87 @x0 @x1) Tm_type)
    :pattern ((HasType (Tm_refine_4763580b8f6d91acfdd99ce186d05f87 @x0 @x1) Tm_type))
    :qid refinement_kinding_Tm_refine_4763580b8f6d91acfdd99ce186d05f87))
  :named refinement_kinding_Tm_refine_4763580b8f6d91acfdd99ce186d05f87))
; refinement_interpretation
;;; Fact-ids: 
(assert
 (! ;; def=Clase01.fst(50,22-50,61); use=Clase01.fst(50,64-50,87)
  (forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 (Tm_refine_4763580b8f6d91acfdd99ce186d05f87 @x2 @x3))
     (and
      (HasTypeFuel @u0 @x1 Prims.int)
      (BoxBool_proj_0
       (Prims.op_BarBar (Prims.op_Equality Prims.int @x1 @x2) (Prims.op_Equality Prims.int @x1 @x3)))
      (BoxBool_proj_0
       (Prims.op_BarBar (Prims.op_GreaterThanOrEqual @x1 @x2) (Prims.op_GreaterThanOrEqual @x1 @x3)))))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_4763580b8f6d91acfdd99ce186d05f87 @x2 @x3)))
    :qid refinement_interpretation_Tm_refine_4763580b8f6d91acfdd99ce186d05f87))
  :named refinement_interpretation_Tm_refine_4763580b8f6d91acfdd99ce186d05f87))
; haseq for Tm_refine_4763580b8f6d91acfdd99ce186d05f87
;;; Fact-ids: 
(assert
 (! ;; def=Clase01.fst(50,22-50,61); use=Clase01.fst(50,64-50,87)
  (forall ((@x0 Term) (@x1 Term))
   (! (iff
     (Valid (Prims.hasEq (Tm_refine_4763580b8f6d91acfdd99ce186d05f87 @x0 @x1)))
     (Valid (Prims.hasEq Prims.int)))
    :pattern ((Valid (Prims.hasEq (Tm_refine_4763580b8f6d91acfdd99ce186d05f87 @x0 @x1))))
    :qid haseqTm_refine_4763580b8f6d91acfdd99ce186d05f87))
  :named haseqTm_refine_4763580b8f6d91acfdd99ce186d05f87))

; Encoding query formula : forall (x: Prims.int) (y: Prims.int).
;   (*  - Could not prove post-condition
; *)
;   forall (k: Prims.pure_post (z: Prims.int{(z = x || z = y) && (z >= x || z >= y)})).
;     (forall (x: z: Prims.int{(z = x || z = y) && (z >= x || z >= y)}).
;         {:pattern Prims.guard_free (k x)}
;         Prims.auto_squash (k x)) ==>
;     (x >= y == true ==> x >= x || x >= y) /\
;     (~(x >= y = true) ==>
;       (forall (b: Prims.bool). x >= y == b ==> (y = x || true) && (y >= x || y >= y)))
; Context: While encoding a query
; While typechecking the top-level declaration `let max`
(push) ;; push{0
; <fuel='2' ifuel='1'>
;;; Fact-ids: 
(assert (! (= MaxFuel (SFuel (SFuel ZFuel))) :named @MaxFuel_assumption))
;;; Fact-ids: 
(assert (! (= MaxIFuel (SFuel ZFuel)) :named @MaxIFuel_assumption))
; query
;;; Fact-ids: 
(assert
 (! (not
   (forall ((@x0 Term) (@x1 Term))
    (! (implies
      (and (HasType @x0 Prims.int) (HasType @x1 Prims.int))
      (forall ((@x2 Term))
       (! (implies
         (and
          (HasType @x2 (Prims.pure_post (Tm_refine_4763580b8f6d91acfdd99ce186d05f87 @x0 @x1)))
          ;; def=Prims.fst(410,27-410,88); use=Clase01.fst(50,64-50,87)
          (forall ((@x3 Term))
           (! ;; def=Prims.fst(410,84-410,87); use=Clase01.fst(50,64-50,87)
            (Valid
             ;; def=Prims.fst(410,84-410,87); use=Clase01.fst(50,64-50,87)
             (ApplyTT @x2 @x3))
            :pattern ((ApplyTT @x2 @x3))
            :qid @query.2)))
         ;; def=Prims.fst(397,2-397,39); use=Clase01.fst(50,64-50,87)
         (and
          (implies
           ;; def=Clase01.fst(50,67-50,73); use=Clase01.fst(50,67-50,73)
           (= (Prims.op_GreaterThanOrEqual @x0 @x1) (BoxBool true))
           ;; def=Clase01.fst(50,29-50,59); use=Clase01.fst(50,79-50,80)
           (or
            label_1
            (BoxBool_proj_0 (Prims.op_GreaterThanOrEqual @x0 @x0))
            (BoxBool_proj_0 (Prims.op_GreaterThanOrEqual @x0 @x1))))
          (implies
           ;; def=Prims.fst(397,19-397,21); use=Clase01.fst(50,64-50,87)
           (not
            ;; def=Clase01.fst(50,67-50,73); use=Clase01.fst(50,67-50,73)
            (= (Prims.op_GreaterThanOrEqual @x0 @x1) (BoxBool true)))
           ;; def=Prims.fst(421,99-421,120); use=Clase01.fst(50,64-50,87)
           (forall ((@x3 Term))
            (! (implies
              (and
               (HasType @x3 Prims.bool)
               ;; def=Clase01.fst(50,67-50,87); use=Clase01.fst(50,67-50,87)
               (= (Prims.op_GreaterThanOrEqual @x0 @x1) @x3))
              ;; def=Clase01.fst(50,29-50,59); use=Clase01.fst(50,86-50,87)
              (and
               ;; def=Clase01.fst(50,11-50,12); use=Clase01.fst(50,86-50,87)
               (or
                label_2
                (BoxBool_proj_0
                 (Prims.op_BarBar (Prims.op_Equality Prims.int @x1 @x0) (BoxBool true))))
               ;; def=Clase01.fst(50,11-50,12); use=Clase01.fst(50,86-50,87)
               (or
                label_3
                (BoxBool_proj_0
                 (Prims.op_BarBar
                  (Prims.op_GreaterThanOrEqual @x1 @x0)
                  (Prims.op_GreaterThanOrEqual @x1 @x1))))))
             :qid @query.3)))))
        :qid @query.1)))
     :qid @query)))
  :named @query))
(set-option :rlimit 2723280)
(echo "<initial_stats>")
(echo "<statistics>") (get-info :all-statistics) (echo "</statistics>")
(echo "</initial_stats>")
(echo "<result>")
(check-sat)
(echo "</result>")
(set-option :rlimit 0)
(echo "<reason-unknown>") (get-info :reason-unknown) (echo "</reason-unknown>")
(echo "<labels>")
(echo "label_3")
(eval label_3)
(echo "label_2")
(eval label_2)
(echo "label_1")
(eval label_1)
(echo "</labels>")
(echo "Done!")
(pop) ;; 0}pop

; QUERY ID: (Clase01.max, 1)
; STATUS: unsat
; Z3 invocation started by F*
; F* version: 2025.08.07~dev -- commit hash: unset
; Z3 version (according to F*): 4.8.5

(pop) ;; 2}pop
; encoding sigelt let max
; <Start encoding let max>
(declare-fun Clase01.max (Term Term) Term)
(declare-fun Tm_refine_4763580b8f6d91acfdd99ce186d05f87 (Term Term) Term)
; x: Prims.int -> y: Prims.int -> z: Prims.int{(z = x || z = y) && (z >= x || z >= y)}
(declare-fun Tm_arrow_86c77c0c3fadb8a48c3f6a76eb1f48e3 () Term)
(declare-fun Clase01.max@tok () Term)

; </end encoding let max>

; well-founded ordering on nat (alt)
;;; Fact-ids: Name Prims.int; Namespace Prims
(assert
 (! (forall ((@u0 Fuel) (@x1 Term) (@x2 Term))
   (! (implies
     (and
      (HasTypeFuel @u0 @x1 Prims.int)
      (HasTypeFuel @u0 @x2 Prims.int)
      (> (BoxInt_proj_0 @x1) 0)
      (>= (BoxInt_proj_0 @x2) 0)
      (< (BoxInt_proj_0 @x2) (BoxInt_proj_0 @x1)))
     (Valid (Prims.precedes Prims.lex_t Prims.lex_t @x2 @x1)))
    :pattern
     ((HasTypeFuel @u0 @x1 Prims.int)
      (HasTypeFuel @u0 @x2 Prims.int)
      (Valid (Prims.precedes Prims.lex_t Prims.lex_t @x2 @x1)))
    :qid well-founded-ordering-on-nat))
  :named well-founded-ordering-on-nat))
;;; Fact-ids: Name Prims.op_Subtraction; Namespace Prims
(assert
 (! ;; def=Prims.fst(554,4-554,18); use=Prims.fst(554,4-554,18)
  (forall ((@x0 Term) (@x1 Term))
   (! (= (Prims.op_Subtraction @x0 @x1) (BoxInt (- (BoxInt_proj_0 @x0) (BoxInt_proj_0 @x1))))
    :pattern ((Prims.op_Subtraction @x0 @x1))
    :qid primitive_Prims.op_Subtraction))
  :named primitive_Prims.op_Subtraction))
(push) ;; push{2
; Starting query at Clase01.fst(58,28-61,52)
; x : Prims.int (Prims.int)
(declare-fun x_ae567c2fb75be05905677af440075565_0 () Term)
; binder_x_ae567c2fb75be05905677af440075565_0
;;; Fact-ids: 
(assert
 (! (HasType x_ae567c2fb75be05905677af440075565_0 Prims.int)
  :named binder_x_ae567c2fb75be05905677af440075565_0))
(declare-fun Tm_refine_c117e3dfa0913e9570f652c9d3f27f5b () Term)
; refinement kinding
;;; Fact-ids: 
(assert
 (! (HasType Tm_refine_c117e3dfa0913e9570f652c9d3f27f5b Tm_type)
  :named refinement_kinding_Tm_refine_c117e3dfa0913e9570f652c9d3f27f5b))
; refinement_interpretation
;;; Fact-ids: 
(assert
 (! ;; def=Clase01.fst(58,13-61,52); use=Clase01.fst(58,13-61,52)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 Tm_refine_c117e3dfa0913e9570f652c9d3f27f5b)
     (and
      (HasTypeFuel @u0 @x1 Prims.int)
      ;; def=Clase01.fst(58,28-61,52); use=Clase01.fst(58,28-61,52)
      ;; def=Clase01.fst(58,28-61,52); use=Clase01.fst(58,28-61,52)
      (Valid
       ;; def=Clase01.fst(58,28-61,52); use=Clase01.fst(58,28-61,52)
       (Prims.precedes Prims.int Prims.int @x1 x_ae567c2fb75be05905677af440075565_0))))
    :pattern ((HasTypeFuel @u0 @x1 Tm_refine_c117e3dfa0913e9570f652c9d3f27f5b))
    :qid refinement_interpretation_Tm_refine_c117e3dfa0913e9570f652c9d3f27f5b))
  :named refinement_interpretation_Tm_refine_c117e3dfa0913e9570f652c9d3f27f5b))
; haseq for Tm_refine_c117e3dfa0913e9570f652c9d3f27f5b
;;; Fact-ids: 
(assert
 (! (iff
   (Valid (Prims.hasEq Tm_refine_c117e3dfa0913e9570f652c9d3f27f5b))
   (Valid (Prims.hasEq Prims.int)))
  :named haseqTm_refine_c117e3dfa0913e9570f652c9d3f27f5b))
(declare-fun Clase01.fib (Term) Term)

; x: Prims.int{x << x} -> Prims.int
(declare-fun Tm_arrow_8fde8981455bc1eda2128516b9fd30a6 () Term)
; kinding_Tm_arrow_8fde8981455bc1eda2128516b9fd30a6
;;; Fact-ids: 
(assert
 (! (HasType Tm_arrow_8fde8981455bc1eda2128516b9fd30a6 Tm_type)
  :named kinding_Tm_arrow_8fde8981455bc1eda2128516b9fd30a6))
; pre-typing for functions
;;; Fact-ids: 
(assert
 (! ;; def=Clase01.fst(58,13-61,52); use=Clase01.fst(58,13-61,52)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (implies
     (HasTypeFuel @u0 @x1 Tm_arrow_8fde8981455bc1eda2128516b9fd30a6)
     (is-Tm_arrow (PreType @x1)))
    :pattern ((HasTypeFuel @u0 @x1 Tm_arrow_8fde8981455bc1eda2128516b9fd30a6))
    :qid Clase01_pre_typing_Tm_arrow_8fde8981455bc1eda2128516b9fd30a6))
  :named Clase01_pre_typing_Tm_arrow_8fde8981455bc1eda2128516b9fd30a6))
; interpretation_Tm_arrow_8fde8981455bc1eda2128516b9fd30a6
;;; Fact-ids: 
(assert
 (! ;; def=Clase01.fst(58,13-61,52); use=Clase01.fst(58,13-61,52)
  (forall ((@x0 Term))
   (! (iff
     (HasTypeZ @x0 Tm_arrow_8fde8981455bc1eda2128516b9fd30a6)
     (and
      ;; def=Clase01.fst(58,13-61,52); use=Clase01.fst(58,13-61,52)
      (forall ((@x1 Term))
       (! (implies
         (HasType @x1 Tm_refine_c117e3dfa0913e9570f652c9d3f27f5b)
         (HasType (ApplyTT @x0 @x1) Prims.int))
        :pattern ((ApplyTT @x0 @x1))
        :qid Clase01_interpretation_Tm_arrow_8fde8981455bc1eda2128516b9fd30a6.1))
      (IsTotFun @x0)))
    :pattern ((HasTypeZ @x0 Tm_arrow_8fde8981455bc1eda2128516b9fd30a6))
    :qid Clase01_interpretation_Tm_arrow_8fde8981455bc1eda2128516b9fd30a6))
  :named Clase01_interpretation_Tm_arrow_8fde8981455bc1eda2128516b9fd30a6))
(declare-fun Clase01.fib@tok () Term)
; Name-token correspondence
;;; Fact-ids: 
(assert
 (! ;; def=Clase01.fst(58,8-58,11); use=Clase01.fst(58,8-58,11)
  (forall ((@x0 Term))
   (! (= (ApplyTT Clase01.fib@tok @x0) (Clase01.fib @x0))
    :pattern ((ApplyTT Clase01.fib@tok @x0))
    :qid token_correspondence_Clase01.fib))
  :named token_correspondence_Clase01.fib))
; function token typing
;;; Fact-ids: 
(assert
 (! ;; def=Clase01.fst(58,8-58,11); use=Clase01.fst(58,8-58,11)
  (forall ((@x0 Term))
   (! (and
     (NoHoist @x0 (HasType Clase01.fib@tok Tm_arrow_8fde8981455bc1eda2128516b9fd30a6))
     ;; def=Clase01.fst(58,8-58,11); use=Clase01.fst(58,8-58,11)
     (forall ((@x1 Term))
      (! (= (ApplyTT Clase01.fib@tok @x1) (Clase01.fib @x1))
       :pattern ((Clase01.fib @x1))
       :qid function_token_typing_Clase01.fib.1)))
    :pattern ((ApplyTT @x0 Clase01.fib@tok))
    :qid function_token_typing_Clase01.fib))
  :named function_token_typing_Clase01.fib))
; free var typing
;;; Fact-ids: 
(assert
 (! ;; def=Clase01.fst(58,8-58,11); use=Clase01.fst(58,8-58,11)
  (forall ((@x0 Term))
   (! (implies
     (HasType @x0 Tm_refine_c117e3dfa0913e9570f652c9d3f27f5b)
     (HasType (Clase01.fib @x0) Prims.int))
    :pattern ((Clase01.fib @x0))
    :qid typing_Clase01.fib))
  :named typing_Clase01.fib))
(declare-fun label_2 () Bool)
(declare-fun label_1 () Bool)

; Encoding query formula : forall (k: Prims.pure_post Prims.int).
;   (forall (x: Prims.int). {:pattern Prims.guard_free (k x)} Prims.auto_squash (k x)) ==>
;   ~(x = 0) ==>
;   ~(x = 1) ==>
;   (forall (b: Prims.int).
;       x == b ==>
;       (forall (k: Prims.pure_post Prims.int).
;           (forall (x: Prims.int). {:pattern Prims.guard_free (k x)} Prims.auto_squash (k x)) ==>
;           b >= 0 == true ==>
;           b - 1 << x /\
;           (forall (return_val: x: Prims.int{x << x}).
;               return_val == b - 1 ==>
;               (forall (any_result: Prims.int). Clase01.fib (b - 1) == any_result ==> b - 2 << x))))
; Context: While encoding a query
; While typechecking the top-level declaration `let rec fib`
(push) ;; push{0
; <fuel='2' ifuel='1'>
;;; Fact-ids: 
(assert (! (= MaxFuel (SFuel (SFuel ZFuel))) :named @MaxFuel_assumption))
;;; Fact-ids: 
(assert (! (= MaxIFuel (SFuel ZFuel)) :named @MaxIFuel_assumption))
; query
;;; Fact-ids: 
(assert
 (! (not
   (forall ((@x0 Term))
    (! (implies
      (and
       (HasType @x0 (Prims.pure_post Prims.int))
       ;; def=Prims.fst(410,27-410,88); use=Clase01.fst(58,28-61,52)
       (forall ((@x1 Term))
        (! ;; def=Prims.fst(410,84-410,87); use=Clase01.fst(58,28-61,52)
         (Valid
          ;; def=Prims.fst(410,84-410,87); use=Clase01.fst(58,28-61,52)
          (ApplyTT @x0 @x1))
         :pattern ((ApplyTT @x0 @x1))
         :qid @query.1))
       ;; def=Prims.fst(397,19-397,21); use=Clase01.fst(58,28-61,52)
       (not
        ;; def=Clase01.fst(58,13-59,5); use=Clase01.fst(58,34-59,5)
        (= x_ae567c2fb75be05905677af440075565_0 (BoxInt 0)))
       ;; def=Prims.fst(397,19-397,21); use=Clase01.fst(58,28-61,52)
       (not
        ;; def=Clase01.fst(58,13-60,5); use=Clase01.fst(58,34-60,5)
        (= x_ae567c2fb75be05905677af440075565_0 (BoxInt 1))))
      ;; def=Prims.fst(421,99-421,120); use=Clase01.fst(58,28-61,52)
      (forall ((@x1 Term))
       (! (implies
         (and
          (HasType @x1 Prims.int)
          ;; def=Clase01.fst(58,13-61,5); use=Clase01.fst(58,34-61,5)
          (= x_ae567c2fb75be05905677af440075565_0 @x1))
         (forall ((@x2 Term))
          (! (implies
            (and
             (HasType @x2 (Prims.pure_post Prims.int))
             ;; def=Prims.fst(410,27-410,88); use=Clase01.fst(58,28-61,52)
             (forall ((@x3 Term))
              (! ;; def=Prims.fst(410,84-410,87); use=Clase01.fst(58,28-61,52)
               (Valid
                ;; def=Prims.fst(410,84-410,87); use=Clase01.fst(58,28-61,52)
                (ApplyTT @x2 @x3))
               :pattern ((ApplyTT @x2 @x3))
               :qid @query.4))
             ;; def=Clase01.fst(61,12-61,18); use=Clase01.fst(61,12-61,18)
             (= (Prims.op_GreaterThanOrEqual @x1 (BoxInt 0)) (BoxBool true)))
            ;; def=Prims.fst(467,77-467,89); use=Clase01.fst(58,28-61,52)
            (and
             ;; def=Clase01.fst(58,28-61,52); use=Clase01.fst(61,28-61,33)
             (or
              label_1
              ;; def=Clase01.fst(58,28-61,52); use=Clase01.fst(61,28-61,33)
              (Valid
               ;; def=Clase01.fst(58,28-61,52); use=Clase01.fst(61,28-61,33)
               (Prims.precedes
                Prims.int
                Prims.int
                (Prims.op_Subtraction @x1 (BoxInt 1))
                x_ae567c2fb75be05905677af440075565_0)))
             ;; def=Prims.fst(364,2-364,58); use=Clase01.fst(58,28-61,52)
             (forall ((@x3 Term))
              (! (implies
                (and
                 (HasType @x3 Tm_refine_c117e3dfa0913e9570f652c9d3f27f5b)
                 ;; def=Prims.fst(364,26-364,41); use=Clase01.fst(58,28-61,52)
                 (= @x3 (Prims.op_Subtraction @x1 (BoxInt 1))))
                ;; def=Prims.fst(459,66-459,102); use=Clase01.fst(58,28-61,52)
                (forall ((@x4 Term))
                 (! (implies
                   (and
                    (HasType @x4 Prims.int)
                    ;; def=dummy(0,0-0,0); use=Clase01.fst(58,28-61,52)
                    (= (Clase01.fib (Prims.op_Subtraction @x1 (BoxInt 1))) @x4))
                   ;; def=Clase01.fst(58,28-61,52); use=Clase01.fst(61,40-61,45)
                   (or
                    label_2
                    ;; def=Clase01.fst(58,28-61,52); use=Clase01.fst(61,40-61,45)
                    (Valid
                     ;; def=Clase01.fst(58,28-61,52); use=Clase01.fst(61,40-61,45)
                     (Prims.precedes
                      Prims.int
                      Prims.int
                      (Prims.op_Subtraction @x1 (BoxInt 2))
                      x_ae567c2fb75be05905677af440075565_0))))
                  :qid @query.6)))
               :qid @query.5))))
           :qid @query.3)))
        :qid @query.2)))
     :qid @query)))
  :named @query))
(set-option :rlimit 2723280)
(echo "<initial_stats>")
(echo "<statistics>") (get-info :all-statistics) (echo "</statistics>")
(echo "</initial_stats>")
(echo "<result>")
(check-sat)
(echo "</result>")
(set-option :rlimit 0)
(echo "<reason-unknown>") (get-info :reason-unknown) (echo "</reason-unknown>")
(echo "<labels>")
(echo "label_2")
(eval label_2)
(echo "label_1")
(eval label_1)
(echo "</labels>")
(echo "Done!")
(pop) ;; 0}pop

; QUERY ID: (Clase01.fib, 1)
; STATUS: unsat
; Z3 invocation started by F*
; F* version: 2025.08.07~dev -- commit hash: unset
; Z3 version (according to F*): 4.8.5

(pop) ;; 2}pop
; encoding sigelt let rec fib
; <Start encoding let rec fib>
; Fuel-instrumented function name
(declare-fun Clase01.fib.fuel_instrumented (Fuel Term) Term)
; Token for fuel-instrumented partial applications
(declare-fun Clase01.fib.fuel_instrumented_token () Term)
(declare-fun Clase01.fib (Term) Term)
(declare-fun Clase01.fib@tok () Term)

; </end encoding let rec fib>

; encoding sigelt let digito
; <Start encoding let digito>
(declare-fun Clase01.digito () Term)
(declare-fun Tm_refine_9c3b9122d9928d7b6fdcfea4e91458fa () Term)
; </end encoding let digito>

; free var typing
;;; Fact-ids: Name Clase01.max; Namespace Clase01
(assert
 (! ;; def=Clase01.fst(50,4-50,7); use=Clase01.fst(50,4-50,7)
  (forall ((@x0 Term) (@x1 Term))
   (! (implies
     (and (HasType @x0 Prims.int) (HasType @x1 Prims.int))
     (HasType (Clase01.max @x0 @x1) (Tm_refine_4763580b8f6d91acfdd99ce186d05f87 @x0 @x1)))
    :pattern ((Clase01.max @x0 @x1))
    :qid typing_Clase01.max))
  :named typing_Clase01.max))
; free var typing
;;; Fact-ids: Name Clase01.digito; Namespace Clase01
(assert
 (! (HasType Clase01.digito Tm_type) :named typing_Clase01.digito))
; refinement kinding
;;; Fact-ids: Name Clase01.digito; Namespace Clase01
(assert
 (! (HasType Tm_refine_9c3b9122d9928d7b6fdcfea4e91458fa Tm_type)
  :named refinement_kinding_Tm_refine_9c3b9122d9928d7b6fdcfea4e91458fa))
; refinement kinding
;;; Fact-ids: Name Clase01.max; Namespace Clase01
(assert
 (! ;; def=Clase01.fst(50,22-50,61); use=Clase01.fst(50,22-50,61)
  (forall ((@x0 Term) (@x1 Term))
   (! (HasType (Tm_refine_4763580b8f6d91acfdd99ce186d05f87 @x0 @x1) Tm_type)
    :pattern ((HasType (Tm_refine_4763580b8f6d91acfdd99ce186d05f87 @x0 @x1) Tm_type))
    :qid refinement_kinding_Tm_refine_4763580b8f6d91acfdd99ce186d05f87))
  :named refinement_kinding_Tm_refine_4763580b8f6d91acfdd99ce186d05f87))
; refinement_interpretation
;;; Fact-ids: Name Clase01.digito; Namespace Clase01
(assert
 (! ;; def=Clase01.fst(64,14-64,37); use=Clase01.fst(64,14-64,37)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 Tm_refine_9c3b9122d9928d7b6fdcfea4e91458fa)
     (and
      (HasTypeFuel @u0 @x1 Prims.nat)
      ;; def=Clase01.fst(64,20-64,26); use=Clase01.fst(64,20-64,26)
      (>= (BoxInt_proj_0 @x1) (BoxInt_proj_0 (BoxInt 0)))
      ;; def=Clase01.fst(64,30-64,36); use=Clase01.fst(64,30-64,36)
      (< (BoxInt_proj_0 @x1) (BoxInt_proj_0 (BoxInt 10)))))
    :pattern ((HasTypeFuel @u0 @x1 Tm_refine_9c3b9122d9928d7b6fdcfea4e91458fa))
    :qid refinement_interpretation_Tm_refine_9c3b9122d9928d7b6fdcfea4e91458fa))
  :named refinement_interpretation_Tm_refine_9c3b9122d9928d7b6fdcfea4e91458fa))
; refinement_interpretation
;;; Fact-ids: Name Clase01.max; Namespace Clase01
(assert
 (! ;; def=Clase01.fst(50,22-50,61); use=Clase01.fst(50,22-50,61)
  (forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 (Tm_refine_4763580b8f6d91acfdd99ce186d05f87 @x2 @x3))
     (and
      (HasTypeFuel @u0 @x1 Prims.int)
      (BoxBool_proj_0
       (Prims.op_BarBar (Prims.op_Equality Prims.int @x1 @x2) (Prims.op_Equality Prims.int @x1 @x3)))
      (BoxBool_proj_0
       (Prims.op_BarBar (Prims.op_GreaterThanOrEqual @x1 @x2) (Prims.op_GreaterThanOrEqual @x1 @x3)))))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_4763580b8f6d91acfdd99ce186d05f87 @x2 @x3)))
    :qid refinement_interpretation_Tm_refine_4763580b8f6d91acfdd99ce186d05f87))
  :named refinement_interpretation_Tm_refine_4763580b8f6d91acfdd99ce186d05f87))
; haseq for Tm_refine_9c3b9122d9928d7b6fdcfea4e91458fa
;;; Fact-ids: Name Clase01.digito; Namespace Clase01
(assert
 (! (iff
   (Valid (Prims.hasEq Tm_refine_9c3b9122d9928d7b6fdcfea4e91458fa))
   (Valid (Prims.hasEq Prims.nat)))
  :named haseqTm_refine_9c3b9122d9928d7b6fdcfea4e91458fa))
; haseq for Tm_refine_4763580b8f6d91acfdd99ce186d05f87
;;; Fact-ids: Name Clase01.max; Namespace Clase01
(assert
 (! ;; def=Clase01.fst(50,22-50,61); use=Clase01.fst(50,22-50,61)
  (forall ((@x0 Term) (@x1 Term))
   (! (iff
     (Valid (Prims.hasEq (Tm_refine_4763580b8f6d91acfdd99ce186d05f87 @x0 @x1)))
     (Valid (Prims.hasEq Prims.int)))
    :pattern ((Valid (Prims.hasEq (Tm_refine_4763580b8f6d91acfdd99ce186d05f87 @x0 @x1))))
    :qid haseqTm_refine_4763580b8f6d91acfdd99ce186d05f87))
  :named haseqTm_refine_4763580b8f6d91acfdd99ce186d05f87))
; function token typing
;;; Fact-ids: Name Clase01.digito; Namespace Clase01
(assert
 (! (HasType Clase01.digito Tm_type) :named function_token_typing_Clase01.digito))
; Equation for Clase01.max
;;; Fact-ids: Name Clase01.max; Namespace Clase01
(assert
 (! ;; def=Clase01.fst(50,4-50,7); use=Clase01.fst(50,4-50,7)
  (forall ((@x0 Term) (@x1 Term))
   (! (=
     (Clase01.max @x0 @x1)
     (let ((@lb2 (Prims.op_GreaterThanOrEqual @x0 @x1))) (ite (= @lb2 (BoxBool true)) @x0 @x1)))
    :pattern ((Clase01.max @x0 @x1))
    :qid equation_Clase01.max))
  :named equation_Clase01.max))
; Equation for Clase01.digito
;;; Fact-ids: Name Clase01.digito; Namespace Clase01
(assert
 (! (= Clase01.digito Tm_refine_9c3b9122d9928d7b6fdcfea4e91458fa) :named equation_Clase01.digito))
(push) ;; push{2
; Starting query at Clase01.fst(71,43-71,58)
(declare-fun label_3 () Bool)
(declare-fun label_2 () Bool)
(declare-fun label_1 () Bool)
; Encoding query formula : forall (x: Clase01.digito) (y: Clase01.digito) (z: Clase01.digito).
;   (*  - Could not prove post-condition
; *)
;   (Clase01.max (Clase01.max x y) z = Clase01.max x y || Clase01.max (Clase01.max x y) z = z) &&
;   (Clase01.max (Clase01.max x y) z >= Clase01.max x y || Clase01.max (Clase01.max x y) z >= z) ==>
;   Clase01.max (Clase01.max x y) z >= 0 /\
;   (Clase01.max (Clase01.max x y) z >= 0) /\ (Clase01.max (Clase01.max x y) z < 10)
; Context: While encoding a query
; While typechecking the top-level declaration `let max_digito`
(push) ;; push{0
; <fuel='2' ifuel='1'>
;;; Fact-ids: 
(assert (! (= MaxFuel (SFuel (SFuel ZFuel))) :named @MaxFuel_assumption))
;;; Fact-ids: 
(assert (! (= MaxIFuel (SFuel ZFuel)) :named @MaxIFuel_assumption))
; query
;;; Fact-ids: 
(assert
 (! (not
   (forall ((@x0 Term) (@x1 Term) (@x2 Term))
    (! (implies
      (and
       (HasType @x0 Clase01.digito)
       (HasType @x1 Clase01.digito)
       (HasType @x2 Clase01.digito)
       (BoxBool_proj_0
        (Prims.op_BarBar
         (Prims.op_Equality Prims.int (Clase01.max (Clase01.max @x0 @x1) @x2) (Clase01.max @x0 @x1))
         (Prims.op_Equality Prims.int (Clase01.max (Clase01.max @x0 @x1) @x2) @x2)))
       (BoxBool_proj_0
        (Prims.op_BarBar
         (Prims.op_GreaterThanOrEqual (Clase01.max (Clase01.max @x0 @x1) @x2) (Clase01.max @x0 @x1))
         (Prims.op_GreaterThanOrEqual (Clase01.max (Clase01.max @x0 @x1) @x2) @x2))))
      ;; def=Clase01.fst(64,20-64,36); use=Clase01.fst(71,43-71,58)
      (and
       ;; def=Prims.fst(682,18-682,24); use=Clase01.fst(71,43-71,58)
       (or
        label_1
        ;; def=Prims.fst(682,18-682,24); use=Clase01.fst(71,43-71,58)
        (>= (BoxInt_proj_0 (Clase01.max (Clase01.max @x0 @x1) @x2)) (BoxInt_proj_0 (BoxInt 0))))
       ;; def=Clase01.fst(64,20-64,26); use=Clase01.fst(71,43-71,58)
       (or
        label_2
        ;; def=Clase01.fst(64,20-64,26); use=Clase01.fst(71,43-71,58)
        (>= (BoxInt_proj_0 (Clase01.max (Clase01.max @x0 @x1) @x2)) (BoxInt_proj_0 (BoxInt 0))))
       ;; def=Clase01.fst(64,30-64,36); use=Clase01.fst(71,43-71,58)
       (or
        label_3
        ;; def=Clase01.fst(64,30-64,36); use=Clase01.fst(71,43-71,58)
        (< (BoxInt_proj_0 (Clase01.max (Clase01.max @x0 @x1) @x2)) (BoxInt_proj_0 (BoxInt 10))))))
     :qid @query)))
  :named @query))
(set-option :rlimit 2723280)
(echo "<initial_stats>")
(echo "<statistics>") (get-info :all-statistics) (echo "</statistics>")
(echo "</initial_stats>")
(echo "<result>")
(check-sat)
(echo "</result>")
(set-option :rlimit 0)
(echo "<reason-unknown>") (get-info :reason-unknown) (echo "</reason-unknown>")
(echo "<labels>")
(echo "label_3")
(eval label_3)
(echo "label_2")
(eval label_2)
(echo "label_1")
(eval label_1)
(echo "</labels>")
(echo "Done!")
(pop) ;; 0}pop

; QUERY ID: (Clase01.max_digito, 1)
; STATUS: unsat
; Z3 invocation started by F*
; F* version: 2025.08.07~dev -- commit hash: unset
; Z3 version (according to F*): 4.8.5

(pop) ;; 2}pop
; encoding sigelt let max_digito
; <Start encoding let max_digito>
(declare-fun Clase01.max_digito (Term Term Term) Term)
; x: digito -> y: digito -> z: digito -> digito
(declare-fun Tm_arrow_e267d15db0310c75d1a80e42d7044db2 () Term)
(declare-fun Clase01.max_digito@tok () Term)
; </end encoding let max_digito>

;;; Fact-ids: Name Prims.op_Multiply; Namespace Prims
(assert
 (! ;; def=Prims.fst(548,4-548,15); use=Prims.fst(548,4-548,15)
  (forall ((@x0 Term) (@x1 Term))
   (! (= (Prims.op_Multiply @x0 @x1) (BoxInt (* (BoxInt_proj_0 @x0) (BoxInt_proj_0 @x1))))
    :pattern ((Prims.op_Multiply @x0 @x1))
    :qid primitive_Prims.op_Multiply))
  :named primitive_Prims.op_Multiply))
;;; Fact-ids: Name Prims.op_LessThanOrEqual; Namespace Prims
(assert
 (! ;; def=Prims.fst(572,4-572,22); use=Prims.fst(572,4-572,22)
  (forall ((@x0 Term) (@x1 Term))
   (! (= (Prims.op_LessThanOrEqual @x0 @x1) (BoxBool (<= (BoxInt_proj_0 @x0) (BoxInt_proj_0 @x1))))
    :pattern ((Prims.op_LessThanOrEqual @x0 @x1))
    :qid primitive_Prims.op_LessThanOrEqual))
  :named primitive_Prims.op_LessThanOrEqual))
(push) ;; push{2
; Starting query at Clase01.fst(74,28-74,63)
; x : Prims.nat (Prims.nat)
(declare-fun x_bb4e1c9af0265270f8e7a5f250f730e2_0 () Term)
; binder_x_bb4e1c9af0265270f8e7a5f250f730e2_0
;;; Fact-ids: 
(assert
 (! (HasType x_bb4e1c9af0265270f8e7a5f250f730e2_0 Prims.nat)
  :named binder_x_bb4e1c9af0265270f8e7a5f250f730e2_0))
(declare-fun Tm_refine_b0ca6e96b7a87a0480fe752315aefe67 () Term)
; refinement kinding
;;; Fact-ids: 
(assert
 (! (HasType Tm_refine_b0ca6e96b7a87a0480fe752315aefe67 Tm_type)
  :named refinement_kinding_Tm_refine_b0ca6e96b7a87a0480fe752315aefe67))
; refinement_interpretation
;;; Fact-ids: 
(assert
 (! ;; def=Clase01.fst(74,13-74,63); use=Clase01.fst(74,13-74,63)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 Tm_refine_b0ca6e96b7a87a0480fe752315aefe67)
     (and
      (HasTypeFuel @u0 @x1 Prims.nat)
      ;; def=Clase01.fst(74,28-74,63); use=Clase01.fst(74,28-74,63)
      ;; def=Clase01.fst(74,28-74,63); use=Clase01.fst(74,28-74,63)
      (Valid
       ;; def=Clase01.fst(74,28-74,63); use=Clase01.fst(74,28-74,63)
       (Prims.precedes Prims.nat Prims.nat @x1 x_bb4e1c9af0265270f8e7a5f250f730e2_0))))
    :pattern ((HasTypeFuel @u0 @x1 Tm_refine_b0ca6e96b7a87a0480fe752315aefe67))
    :qid refinement_interpretation_Tm_refine_b0ca6e96b7a87a0480fe752315aefe67))
  :named refinement_interpretation_Tm_refine_b0ca6e96b7a87a0480fe752315aefe67))
; haseq for Tm_refine_b0ca6e96b7a87a0480fe752315aefe67
;;; Fact-ids: 
(assert
 (! (iff
   (Valid (Prims.hasEq Tm_refine_b0ca6e96b7a87a0480fe752315aefe67))
   (Valid (Prims.hasEq Prims.nat)))
  :named haseqTm_refine_b0ca6e96b7a87a0480fe752315aefe67))
(declare-fun Clase01.fac (Term) Term)

; x: Prims.nat{x << x} -> Prims.nat
(declare-fun Tm_arrow_9af36e09e39d185cf782e366b3502d27 () Term)
; kinding_Tm_arrow_9af36e09e39d185cf782e366b3502d27
;;; Fact-ids: 
(assert
 (! (HasType Tm_arrow_9af36e09e39d185cf782e366b3502d27 Tm_type)
  :named kinding_Tm_arrow_9af36e09e39d185cf782e366b3502d27))
; pre-typing for functions
;;; Fact-ids: 
(assert
 (! ;; def=Clase01.fst(74,13-74,63); use=Clase01.fst(74,13-74,63)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (implies
     (HasTypeFuel @u0 @x1 Tm_arrow_9af36e09e39d185cf782e366b3502d27)
     (is-Tm_arrow (PreType @x1)))
    :pattern ((HasTypeFuel @u0 @x1 Tm_arrow_9af36e09e39d185cf782e366b3502d27))
    :qid Clase01_pre_typing_Tm_arrow_9af36e09e39d185cf782e366b3502d27))
  :named Clase01_pre_typing_Tm_arrow_9af36e09e39d185cf782e366b3502d27))
; interpretation_Tm_arrow_9af36e09e39d185cf782e366b3502d27
;;; Fact-ids: 
(assert
 (! ;; def=Clase01.fst(74,13-74,63); use=Clase01.fst(74,13-74,63)
  (forall ((@x0 Term))
   (! (iff
     (HasTypeZ @x0 Tm_arrow_9af36e09e39d185cf782e366b3502d27)
     (and
      ;; def=Clase01.fst(74,13-74,63); use=Clase01.fst(74,13-74,63)
      (forall ((@x1 Term))
       (! (implies
         (HasType @x1 Tm_refine_b0ca6e96b7a87a0480fe752315aefe67)
         (HasType (ApplyTT @x0 @x1) Prims.nat))
        :pattern ((ApplyTT @x0 @x1))
        :qid Clase01_interpretation_Tm_arrow_9af36e09e39d185cf782e366b3502d27.1))
      (IsTotFun @x0)))
    :pattern ((HasTypeZ @x0 Tm_arrow_9af36e09e39d185cf782e366b3502d27))
    :qid Clase01_interpretation_Tm_arrow_9af36e09e39d185cf782e366b3502d27))
  :named Clase01_interpretation_Tm_arrow_9af36e09e39d185cf782e366b3502d27))
(declare-fun Clase01.fac@tok () Term)
; Name-token correspondence
;;; Fact-ids: 
(assert
 (! ;; def=Clase01.fst(74,8-74,11); use=Clase01.fst(74,8-74,11)
  (forall ((@x0 Term))
   (! (= (ApplyTT Clase01.fac@tok @x0) (Clase01.fac @x0))
    :pattern ((ApplyTT Clase01.fac@tok @x0))
    :qid token_correspondence_Clase01.fac))
  :named token_correspondence_Clase01.fac))
; function token typing
;;; Fact-ids: 
(assert
 (! ;; def=Clase01.fst(74,8-74,11); use=Clase01.fst(74,8-74,11)
  (forall ((@x0 Term))
   (! (and
     (NoHoist @x0 (HasType Clase01.fac@tok Tm_arrow_9af36e09e39d185cf782e366b3502d27))
     ;; def=Clase01.fst(74,8-74,11); use=Clase01.fst(74,8-74,11)
     (forall ((@x1 Term))
      (! (= (ApplyTT Clase01.fac@tok @x1) (Clase01.fac @x1))
       :pattern ((Clase01.fac @x1))
       :qid function_token_typing_Clase01.fac.1)))
    :pattern ((ApplyTT @x0 Clase01.fac@tok))
    :qid function_token_typing_Clase01.fac))
  :named function_token_typing_Clase01.fac))
; free var typing
;;; Fact-ids: 
(assert
 (! ;; def=Clase01.fst(74,8-74,11); use=Clase01.fst(74,8-74,11)
  (forall ((@x0 Term))
   (! (implies
     (HasType @x0 Tm_refine_b0ca6e96b7a87a0480fe752315aefe67)
     (HasType (Clase01.fac @x0) Prims.nat))
    :pattern ((Clase01.fac @x0))
    :qid typing_Clase01.fac))
  :named typing_Clase01.fac))
(declare-fun label_3 () Bool)
(declare-fun label_2 () Bool)
(declare-fun label_1 () Bool)

; Encoding query formula : forall (k: Prims.pure_post Prims.nat).
;   (forall (x: Prims.nat). {:pattern Prims.guard_free (k x)} Prims.auto_squash (k x)) ==>
;   ~(x <= 1 = true) ==>
;   (forall (b: Prims.bool).
;       x <= 1 == b ==>
;       x - 1 >= 0 /\ x - 1 << x /\
;       (forall (return_val: x: Prims.nat{x << x}).
;           return_val == x - 1 ==>
;           (forall (any_result: Prims.nat).
;               Clase01.fac (x - 1) == any_result ==>
;               (forall (return_val: Prims.nat).
;                   return_val == Clase01.fac (x - 1) ==>
;                   Clase01.fac (x - 1) == return_val ==>
;                   (forall (any_result: Prims.int).
;                       x * Clase01.fac (x - 1) == any_result ==> x * Clase01.fac (x - 1) >= 0)))))
; Context: While encoding a query
; While typechecking the top-level declaration `let rec fac`
(push) ;; push{0
; <fuel='2' ifuel='1'>
;;; Fact-ids: 
(assert (! (= MaxFuel (SFuel (SFuel ZFuel))) :named @MaxFuel_assumption))
;;; Fact-ids: 
(assert (! (= MaxIFuel (SFuel ZFuel)) :named @MaxIFuel_assumption))
; query
;;; Fact-ids: 
(assert
 (! (not
   (forall ((@x0 Term))
    (! (implies
      (and
       (HasType @x0 (Prims.pure_post Prims.nat))
       ;; def=Prims.fst(410,27-410,88); use=Clase01.fst(74,28-74,63)
       (forall ((@x1 Term))
        (! ;; def=Prims.fst(410,84-410,87); use=Clase01.fst(74,28-74,63)
         (Valid
          ;; def=Prims.fst(410,84-410,87); use=Clase01.fst(74,28-74,63)
          (ApplyTT @x0 @x1))
         :pattern ((ApplyTT @x0 @x1))
         :qid @query.1))
       ;; def=Prims.fst(397,19-397,21); use=Clase01.fst(74,28-74,63)
       (not
        ;; def=Clase01.fst(74,31-74,37); use=Clase01.fst(74,31-74,37)
        (= (Prims.op_LessThanOrEqual x_bb4e1c9af0265270f8e7a5f250f730e2_0 (BoxInt 1)) (BoxBool true))))
      ;; def=Prims.fst(421,99-421,120); use=Clase01.fst(74,28-74,63)
      (forall ((@x1 Term))
       (! (implies
         (and
          (HasType @x1 Prims.bool)
          ;; def=Clase01.fst(74,31-74,63); use=Clase01.fst(74,31-74,63)
          (= (Prims.op_LessThanOrEqual x_bb4e1c9af0265270f8e7a5f250f730e2_0 (BoxInt 1)) @x1))
         ;; def=Prims.fst(467,77-467,89); use=Clase01.fst(74,28-74,63)
         (and
          ;; def=Prims.fst(682,18-682,24); use=Clase01.fst(74,58-74,63)
          (or
           label_1
           ;; def=Prims.fst(682,18-682,24); use=Clase01.fst(74,58-74,63)
           (>=
            (BoxInt_proj_0 (Prims.op_Subtraction x_bb4e1c9af0265270f8e7a5f250f730e2_0 (BoxInt 1)))
            (BoxInt_proj_0 (BoxInt 0))))
          ;; def=Clase01.fst(74,28-74,63); use=Clase01.fst(74,58-74,63)
          (or
           label_2
           ;; def=Clase01.fst(74,28-74,63); use=Clase01.fst(74,58-74,63)
           (Valid
            ;; def=Clase01.fst(74,28-74,63); use=Clase01.fst(74,58-74,63)
            (Prims.precedes
             Prims.nat
             Prims.nat
             (Prims.op_Subtraction x_bb4e1c9af0265270f8e7a5f250f730e2_0 (BoxInt 1))
             x_bb4e1c9af0265270f8e7a5f250f730e2_0)))
          ;; def=Prims.fst(364,2-364,58); use=Clase01.fst(74,28-74,63)
          (forall ((@x2 Term))
           (! (implies
             (and
              (HasType @x2 Tm_refine_b0ca6e96b7a87a0480fe752315aefe67)
              ;; def=Prims.fst(364,26-364,41); use=Clase01.fst(74,28-74,63)
              (= @x2 (Prims.op_Subtraction x_bb4e1c9af0265270f8e7a5f250f730e2_0 (BoxInt 1))))
             ;; def=Prims.fst(459,66-459,102); use=Clase01.fst(74,28-74,63)
             (forall ((@x3 Term))
              (! (implies
                (and
                 (HasType @x3 Prims.nat)
                 ;; def=Clase01.fst(74,22-74,63); use=Clase01.fst(74,54-74,63)
                 (=
                  (Clase01.fac
                   (Prims.op_Subtraction x_bb4e1c9af0265270f8e7a5f250f730e2_0 (BoxInt 1)))
                  @x3))
                ;; def=Prims.fst(364,2-364,58); use=Clase01.fst(74,28-74,63)
                (forall ((@x4 Term))
                 (! (implies
                   (and
                    (HasType @x4 Prims.nat)
                    ;; def=Prims.fst(364,26-364,41); use=Clase01.fst(74,28-74,63)
                    (=
                     @x4
                     (Clase01.fac
                      (Prims.op_Subtraction x_bb4e1c9af0265270f8e7a5f250f730e2_0 (BoxInt 1))))
                    ;; def=dummy(0,0-0,0); use=Clase01.fst(74,28-74,63)
                    (=
                     (Clase01.fac
                      (Prims.op_Subtraction x_bb4e1c9af0265270f8e7a5f250f730e2_0 (BoxInt 1)))
                     @x4))
                   ;; def=Prims.fst(459,66-459,102); use=Clase01.fst(74,28-74,63)
                   (forall ((@x5 Term))
                    (! (implies
                      (and
                       (HasType @x5 Prims.int)
                       ;; def=Clase01.fst(74,22-74,63); use=Clase01.fst(74,28-74,63)
                       (=
                        (Prims.op_Multiply
                         x_bb4e1c9af0265270f8e7a5f250f730e2_0
                         (Clase01.fac
                          (Prims.op_Subtraction x_bb4e1c9af0265270f8e7a5f250f730e2_0 (BoxInt 1))))
                        @x5))
                      ;; def=Prims.fst(682,18-682,24); use=Clase01.fst(74,50-74,63)
                      (or
                       label_3
                       ;; def=Prims.fst(682,18-682,24); use=Clase01.fst(74,50-74,63)
                       (>=
                        (BoxInt_proj_0
                         (Prims.op_Multiply
                          x_bb4e1c9af0265270f8e7a5f250f730e2_0
                          (Clase01.fac
                           (Prims.op_Subtraction x_bb4e1c9af0265270f8e7a5f250f730e2_0 (BoxInt 1)))))
                        (BoxInt_proj_0 (BoxInt 0)))))
                     :qid @query.6)))
                  :qid @query.5)))
               :qid @query.4)))
            :qid @query.3))))
        :qid @query.2)))
     :qid @query)))
  :named @query))
(set-option :rlimit 2723280)
(echo "<initial_stats>")
(echo "<statistics>") (get-info :all-statistics) (echo "</statistics>")
(echo "</initial_stats>")
(echo "<result>")
(check-sat)
(echo "</result>")
(set-option :rlimit 0)
(echo "<reason-unknown>") (get-info :reason-unknown) (echo "</reason-unknown>")
(echo "<labels>")
(echo "label_3")
(eval label_3)
(echo "label_2")
(eval label_2)
(echo "label_1")
(eval label_1)
(echo "</labels>")
(echo "Done!")
(pop) ;; 0}pop

; QUERY ID: (Clase01.fac, 1)
; STATUS: unsat
; Z3 invocation started by F*
; F* version: 2025.08.07~dev -- commit hash: unset
; Z3 version (according to F*): 4.8.5

(pop) ;; 2}pop
; encoding sigelt let rec fac
; <Start encoding let rec fac>
; Fuel-instrumented function name
(declare-fun Clase01.fac.fuel_instrumented (Fuel Term) Term)
; Token for fuel-instrumented partial applications
(declare-fun Clase01.fac.fuel_instrumented_token () Term)
(declare-fun Clase01.fac (Term) Term)
(declare-fun Clase01.fac@tok () Term)

; </end encoding let rec fac>

(push) ;; push{2
; Starting query at Clase01.fst(77,31-77,68)
; n : Prims.nat (Prims.nat)
(declare-fun x_bb4e1c9af0265270f8e7a5f250f730e2_0 () Term)
; binder_x_bb4e1c9af0265270f8e7a5f250f730e2_0
;;; Fact-ids: 
(assert
 (! (HasType x_bb4e1c9af0265270f8e7a5f250f730e2_0 Prims.nat)
  :named binder_x_bb4e1c9af0265270f8e7a5f250f730e2_0))
(declare-fun Tm_refine_b0ca6e96b7a87a0480fe752315aefe67 () Term)
; refinement kinding
;;; Fact-ids: 
(assert
 (! (HasType Tm_refine_b0ca6e96b7a87a0480fe752315aefe67 Tm_type)
  :named refinement_kinding_Tm_refine_b0ca6e96b7a87a0480fe752315aefe67))
; refinement_interpretation
;;; Fact-ids: 
(assert
 (! ;; def=Clase01.fst(77,16-77,68); use=Clase01.fst(77,16-77,68)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 Tm_refine_b0ca6e96b7a87a0480fe752315aefe67)
     (and
      (HasTypeFuel @u0 @x1 Prims.nat)
      ;; def=Clase01.fst(77,31-77,68); use=Clase01.fst(77,31-77,68)
      ;; def=Clase01.fst(77,31-77,68); use=Clase01.fst(77,31-77,68)
      (Valid
       ;; def=Clase01.fst(77,31-77,68); use=Clase01.fst(77,31-77,68)
       (Prims.precedes Prims.nat Prims.nat @x1 x_bb4e1c9af0265270f8e7a5f250f730e2_0))))
    :pattern ((HasTypeFuel @u0 @x1 Tm_refine_b0ca6e96b7a87a0480fe752315aefe67))
    :qid refinement_interpretation_Tm_refine_b0ca6e96b7a87a0480fe752315aefe67))
  :named refinement_interpretation_Tm_refine_b0ca6e96b7a87a0480fe752315aefe67))
; haseq for Tm_refine_b0ca6e96b7a87a0480fe752315aefe67
;;; Fact-ids: 
(assert
 (! (iff
   (Valid (Prims.hasEq Tm_refine_b0ca6e96b7a87a0480fe752315aefe67))
   (Valid (Prims.hasEq Prims.nat)))
  :named haseqTm_refine_b0ca6e96b7a87a0480fe752315aefe67))
(declare-fun Clase01.triang (Term) Term)

; n: Prims.nat{n << n} -> Prims.nat
(declare-fun Tm_arrow_9af36e09e39d185cf782e366b3502d27 () Term)
; kinding_Tm_arrow_9af36e09e39d185cf782e366b3502d27
;;; Fact-ids: 
(assert
 (! (HasType Tm_arrow_9af36e09e39d185cf782e366b3502d27 Tm_type)
  :named kinding_Tm_arrow_9af36e09e39d185cf782e366b3502d27))
; pre-typing for functions
;;; Fact-ids: 
(assert
 (! ;; def=Clase01.fst(77,16-77,68); use=Clase01.fst(77,16-77,68)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (implies
     (HasTypeFuel @u0 @x1 Tm_arrow_9af36e09e39d185cf782e366b3502d27)
     (is-Tm_arrow (PreType @x1)))
    :pattern ((HasTypeFuel @u0 @x1 Tm_arrow_9af36e09e39d185cf782e366b3502d27))
    :qid Clase01_pre_typing_Tm_arrow_9af36e09e39d185cf782e366b3502d27))
  :named Clase01_pre_typing_Tm_arrow_9af36e09e39d185cf782e366b3502d27))
; interpretation_Tm_arrow_9af36e09e39d185cf782e366b3502d27
;;; Fact-ids: 
(assert
 (! ;; def=Clase01.fst(77,16-77,68); use=Clase01.fst(77,16-77,68)
  (forall ((@x0 Term))
   (! (iff
     (HasTypeZ @x0 Tm_arrow_9af36e09e39d185cf782e366b3502d27)
     (and
      ;; def=Clase01.fst(77,16-77,68); use=Clase01.fst(77,16-77,68)
      (forall ((@x1 Term))
       (! (implies
         (HasType @x1 Tm_refine_b0ca6e96b7a87a0480fe752315aefe67)
         (HasType (ApplyTT @x0 @x1) Prims.nat))
        :pattern ((ApplyTT @x0 @x1))
        :qid Clase01_interpretation_Tm_arrow_9af36e09e39d185cf782e366b3502d27.1))
      (IsTotFun @x0)))
    :pattern ((HasTypeZ @x0 Tm_arrow_9af36e09e39d185cf782e366b3502d27))
    :qid Clase01_interpretation_Tm_arrow_9af36e09e39d185cf782e366b3502d27))
  :named Clase01_interpretation_Tm_arrow_9af36e09e39d185cf782e366b3502d27))
(declare-fun Clase01.triang@tok () Term)
; Name-token correspondence
;;; Fact-ids: 
(assert
 (! ;; def=Clase01.fst(77,8-77,14); use=Clase01.fst(77,8-77,14)
  (forall ((@x0 Term))
   (! (= (ApplyTT Clase01.triang@tok @x0) (Clase01.triang @x0))
    :pattern ((ApplyTT Clase01.triang@tok @x0))
    :qid token_correspondence_Clase01.triang))
  :named token_correspondence_Clase01.triang))
; function token typing
;;; Fact-ids: 
(assert
 (! ;; def=Clase01.fst(77,8-77,14); use=Clase01.fst(77,8-77,14)
  (forall ((@x0 Term))
   (! (and
     (NoHoist @x0 (HasType Clase01.triang@tok Tm_arrow_9af36e09e39d185cf782e366b3502d27))
     ;; def=Clase01.fst(77,8-77,14); use=Clase01.fst(77,8-77,14)
     (forall ((@x1 Term))
      (! (= (ApplyTT Clase01.triang@tok @x1) (Clase01.triang @x1))
       :pattern ((Clase01.triang @x1))
       :qid function_token_typing_Clase01.triang.1)))
    :pattern ((ApplyTT @x0 Clase01.triang@tok))
    :qid function_token_typing_Clase01.triang))
  :named function_token_typing_Clase01.triang))
; free var typing
;;; Fact-ids: 
(assert
 (! ;; def=Clase01.fst(77,8-77,14); use=Clase01.fst(77,8-77,14)
  (forall ((@x0 Term))
   (! (implies
     (HasType @x0 Tm_refine_b0ca6e96b7a87a0480fe752315aefe67)
     (HasType (Clase01.triang @x0) Prims.nat))
    :pattern ((Clase01.triang @x0))
    :qid typing_Clase01.triang))
  :named typing_Clase01.triang))
(declare-fun label_3 () Bool)
(declare-fun label_2 () Bool)
(declare-fun label_1 () Bool)

; Encoding query formula : forall (k: Prims.pure_post Prims.nat).
;   (forall (x: Prims.nat). {:pattern Prims.guard_free (k x)} Prims.auto_squash (k x)) ==>
;   ~(n = 0 = true) ==>
;   (forall (b: Prims.bool).
;       n = 0 == b ==>
;       n - 1 >= 0 /\ n - 1 << n /\
;       (forall (return_val: n: Prims.nat{n << n}).
;           return_val == n - 1 ==>
;           (forall (any_result: Prims.nat).
;               Clase01.triang (n - 1) == any_result ==>
;               (forall (return_val: Prims.nat).
;                   return_val == Clase01.triang (n - 1) ==>
;                   Clase01.triang (n - 1) == return_val ==>
;                   (forall (any_result: Prims.int).
;                       n + Clase01.triang (n - 1) == any_result ==> n + Clase01.triang (n - 1) >= 0))
;           )))
; Context: While encoding a query
; While typechecking the top-level declaration `let rec triang`
(push) ;; push{0
; <fuel='2' ifuel='1'>
;;; Fact-ids: 
(assert (! (= MaxFuel (SFuel (SFuel ZFuel))) :named @MaxFuel_assumption))
;;; Fact-ids: 
(assert (! (= MaxIFuel (SFuel ZFuel)) :named @MaxIFuel_assumption))
; query
;;; Fact-ids: 
(assert
 (! (not
   (forall ((@x0 Term))
    (! (implies
      (and
       (HasType @x0 (Prims.pure_post Prims.nat))
       ;; def=Prims.fst(410,27-410,88); use=Clase01.fst(77,31-77,68)
       (forall ((@x1 Term))
        (! ;; def=Prims.fst(410,84-410,87); use=Clase01.fst(77,31-77,68)
         (Valid
          ;; def=Prims.fst(410,84-410,87); use=Clase01.fst(77,31-77,68)
          (ApplyTT @x0 @x1))
         :pattern ((ApplyTT @x0 @x1))
         :qid @query.1))
       ;; def=Prims.fst(397,19-397,21); use=Clase01.fst(77,31-77,68)
       (not
        ;; def=Clase01.fst(77,34-77,39); use=Clase01.fst(77,34-77,39)
        (=
         (Prims.op_Equality Prims.int x_bb4e1c9af0265270f8e7a5f250f730e2_0 (BoxInt 0))
         (BoxBool true))))
      ;; def=Prims.fst(421,99-421,120); use=Clase01.fst(77,31-77,68)
      (forall ((@x1 Term))
       (! (implies
         (and
          (HasType @x1 Prims.bool)
          ;; def=Clase01.fst(77,34-77,68); use=Clase01.fst(77,34-77,68)
          (= (Prims.op_Equality Prims.int x_bb4e1c9af0265270f8e7a5f250f730e2_0 (BoxInt 0)) @x1))
         ;; def=Prims.fst(467,77-467,89); use=Clase01.fst(77,31-77,68)
         (and
          ;; def=Prims.fst(682,18-682,24); use=Clase01.fst(77,63-77,68)
          (or
           label_1
           ;; def=Prims.fst(682,18-682,24); use=Clase01.fst(77,63-77,68)
           (>=
            (BoxInt_proj_0 (Prims.op_Subtraction x_bb4e1c9af0265270f8e7a5f250f730e2_0 (BoxInt 1)))
            (BoxInt_proj_0 (BoxInt 0))))
          ;; def=Clase01.fst(77,31-77,68); use=Clase01.fst(77,63-77,68)
          (or
           label_2
           ;; def=Clase01.fst(77,31-77,68); use=Clase01.fst(77,63-77,68)
           (Valid
            ;; def=Clase01.fst(77,31-77,68); use=Clase01.fst(77,63-77,68)
            (Prims.precedes
             Prims.nat
             Prims.nat
             (Prims.op_Subtraction x_bb4e1c9af0265270f8e7a5f250f730e2_0 (BoxInt 1))
             x_bb4e1c9af0265270f8e7a5f250f730e2_0)))
          ;; def=Prims.fst(364,2-364,58); use=Clase01.fst(77,31-77,68)
          (forall ((@x2 Term))
           (! (implies
             (and
              (HasType @x2 Tm_refine_b0ca6e96b7a87a0480fe752315aefe67)
              ;; def=Prims.fst(364,26-364,41); use=Clase01.fst(77,31-77,68)
              (= @x2 (Prims.op_Subtraction x_bb4e1c9af0265270f8e7a5f250f730e2_0 (BoxInt 1))))
             ;; def=Prims.fst(459,66-459,102); use=Clase01.fst(77,31-77,68)
             (forall ((@x3 Term))
              (! (implies
                (and
                 (HasType @x3 Prims.nat)
                 ;; def=Clase01.fst(77,25-77,68); use=Clase01.fst(77,56-77,68)
                 (=
                  (Clase01.triang
                   (Prims.op_Subtraction x_bb4e1c9af0265270f8e7a5f250f730e2_0 (BoxInt 1)))
                  @x3))
                ;; def=Prims.fst(364,2-364,58); use=Clase01.fst(77,31-77,68)
                (forall ((@x4 Term))
                 (! (implies
                   (and
                    (HasType @x4 Prims.nat)
                    ;; def=Prims.fst(364,26-364,41); use=Clase01.fst(77,31-77,68)
                    (=
                     @x4
                     (Clase01.triang
                      (Prims.op_Subtraction x_bb4e1c9af0265270f8e7a5f250f730e2_0 (BoxInt 1))))
                    ;; def=dummy(0,0-0,0); use=Clase01.fst(77,31-77,68)
                    (=
                     (Clase01.triang
                      (Prims.op_Subtraction x_bb4e1c9af0265270f8e7a5f250f730e2_0 (BoxInt 1)))
                     @x4))
                   ;; def=Prims.fst(459,66-459,102); use=Clase01.fst(77,31-77,68)
                   (forall ((@x5 Term))
                    (! (implies
                      (and
                       (HasType @x5 Prims.int)
                       ;; def=Clase01.fst(77,25-77,68); use=Clase01.fst(77,31-77,68)
                       (=
                        (Prims.op_Addition
                         x_bb4e1c9af0265270f8e7a5f250f730e2_0
                         (Clase01.triang
                          (Prims.op_Subtraction x_bb4e1c9af0265270f8e7a5f250f730e2_0 (BoxInt 1))))
                        @x5))
                      ;; def=Prims.fst(682,18-682,24); use=Clase01.fst(77,52-77,68)
                      (or
                       label_3
                       ;; def=Prims.fst(682,18-682,24); use=Clase01.fst(77,52-77,68)
                       (>=
                        (BoxInt_proj_0
                         (Prims.op_Addition
                          x_bb4e1c9af0265270f8e7a5f250f730e2_0
                          (Clase01.triang
                           (Prims.op_Subtraction x_bb4e1c9af0265270f8e7a5f250f730e2_0 (BoxInt 1)))))
                        (BoxInt_proj_0 (BoxInt 0)))))
                     :qid @query.6)))
                  :qid @query.5)))
               :qid @query.4)))
            :qid @query.3))))
        :qid @query.2)))
     :qid @query)))
  :named @query))
(set-option :rlimit 2723280)
(echo "<initial_stats>")
(echo "<statistics>") (get-info :all-statistics) (echo "</statistics>")
(echo "</initial_stats>")
(echo "<result>")
(check-sat)
(echo "</result>")
(set-option :rlimit 0)
(echo "<reason-unknown>") (get-info :reason-unknown) (echo "</reason-unknown>")
(echo "<labels>")
(echo "label_3")
(eval label_3)
(echo "label_2")
(eval label_2)
(echo "label_1")
(eval label_1)
(echo "</labels>")
(echo "Done!")
(pop) ;; 0}pop

; QUERY ID: (Clase01.triang, 1)
; STATUS: unsat
; Z3 invocation started by F*
; F* version: 2025.08.07~dev -- commit hash: unset
; Z3 version (according to F*): 4.8.5

(pop) ;; 2}pop
; encoding sigelt let rec triang
; <Start encoding let rec triang>
; Fuel-instrumented function name
(declare-fun Clase01.triang.fuel_instrumented (Fuel Term) Term)
; Token for fuel-instrumented partial applications
(declare-fun Clase01.triang.fuel_instrumented_token () Term)
(declare-fun Clase01.triang (Term) Term)
(declare-fun Clase01.triang@tok () Term)

; </end encoding let rec triang>

(push) ;; push{2
; Starting query at Clase01.fst(82,42-85,54)
; x : Prims.int (Prims.int)
(declare-fun x_ae567c2fb75be05905677af440075565_0 () Term)
; binder_x_ae567c2fb75be05905677af440075565_0
;;; Fact-ids: 
(assert
 (! (HasType x_ae567c2fb75be05905677af440075565_0 Prims.int)
  :named binder_x_ae567c2fb75be05905677af440075565_0))
(declare-fun Tm_refine_c117e3dfa0913e9570f652c9d3f27f5b () Term)
; refinement kinding
;;; Fact-ids: 
(assert
 (! (HasType Tm_refine_c117e3dfa0913e9570f652c9d3f27f5b Tm_type)
  :named refinement_kinding_Tm_refine_c117e3dfa0913e9570f652c9d3f27f5b))
; refinement_interpretation
;;; Fact-ids: 
(assert
 (! ;; def=Clase01.fst(82,14-85,54); use=Clase01.fst(82,14-85,54)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 Tm_refine_c117e3dfa0913e9570f652c9d3f27f5b)
     (and
      (HasTypeFuel @u0 @x1 Prims.int)
      ;; def=Clase01.fst(82,42-85,54); use=Clase01.fst(82,42-85,54)
      ;; def=Clase01.fst(82,42-85,54); use=Clase01.fst(82,42-85,54)
      (Valid
       ;; def=Clase01.fst(82,42-85,54); use=Clase01.fst(82,42-85,54)
       (Prims.precedes Prims.int Prims.int @x1 x_ae567c2fb75be05905677af440075565_0))))
    :pattern ((HasTypeFuel @u0 @x1 Tm_refine_c117e3dfa0913e9570f652c9d3f27f5b))
    :qid refinement_interpretation_Tm_refine_c117e3dfa0913e9570f652c9d3f27f5b))
  :named refinement_interpretation_Tm_refine_c117e3dfa0913e9570f652c9d3f27f5b))
; haseq for Tm_refine_c117e3dfa0913e9570f652c9d3f27f5b
;;; Fact-ids: 
(assert
 (! (iff
   (Valid (Prims.hasEq Tm_refine_c117e3dfa0913e9570f652c9d3f27f5b))
   (Valid (Prims.hasEq Prims.int)))
  :named haseqTm_refine_c117e3dfa0913e9570f652c9d3f27f5b))
(declare-fun Clase01.fib_ (Term) Term)

(declare-fun Tm_refine_4f1d92a9a3f071e1fa3026ba94fce31c (Term) Term)
; refinement kinding
;;; Fact-ids: 
(assert
 (! ;; def=Clase01.fst(82,23-82,39); use=Clase01.fst(82,23-82,39)
  (forall ((@x0 Term))
   (! (HasType (Tm_refine_4f1d92a9a3f071e1fa3026ba94fce31c @x0) Tm_type)
    :pattern ((HasType (Tm_refine_4f1d92a9a3f071e1fa3026ba94fce31c @x0) Tm_type))
    :qid refinement_kinding_Tm_refine_4f1d92a9a3f071e1fa3026ba94fce31c))
  :named refinement_kinding_Tm_refine_4f1d92a9a3f071e1fa3026ba94fce31c))
; refinement_interpretation
;;; Fact-ids: 
(assert
 (! ;; def=Clase01.fst(82,23-82,39); use=Clase01.fst(82,23-82,39)
  (forall ((@u0 Fuel) (@x1 Term) (@x2 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 (Tm_refine_4f1d92a9a3f071e1fa3026ba94fce31c @x2))
     (and
      (HasTypeFuel @u0 @x1 Prims.int)
      ;; def=Clase01.fst(82,31-82,37); use=Clase01.fst(82,31-82,37)
      (>= (BoxInt_proj_0 @x1) (BoxInt_proj_0 @x2))))
    :pattern ((HasTypeFuel @u0 @x1 (Tm_refine_4f1d92a9a3f071e1fa3026ba94fce31c @x2)))
    :qid refinement_interpretation_Tm_refine_4f1d92a9a3f071e1fa3026ba94fce31c))
  :named refinement_interpretation_Tm_refine_4f1d92a9a3f071e1fa3026ba94fce31c))
; haseq for Tm_refine_4f1d92a9a3f071e1fa3026ba94fce31c
;;; Fact-ids: 
(assert
 (! ;; def=Clase01.fst(82,23-82,39); use=Clase01.fst(82,23-82,39)
  (forall ((@x0 Term))
   (! (iff
     (Valid (Prims.hasEq (Tm_refine_4f1d92a9a3f071e1fa3026ba94fce31c @x0)))
     (Valid (Prims.hasEq Prims.int)))
    :pattern ((Valid (Prims.hasEq (Tm_refine_4f1d92a9a3f071e1fa3026ba94fce31c @x0))))
    :qid haseqTm_refine_4f1d92a9a3f071e1fa3026ba94fce31c))
  :named haseqTm_refine_4f1d92a9a3f071e1fa3026ba94fce31c))
; x: Prims.int{x << x} -> y: Prims.int{y >= x}
(declare-fun Tm_arrow_19c6f105dd0efded996f72ea7238228d () Term)
; kinding_Tm_arrow_19c6f105dd0efded996f72ea7238228d
;;; Fact-ids: 
(assert
 (! (HasType Tm_arrow_19c6f105dd0efded996f72ea7238228d Tm_type)
  :named kinding_Tm_arrow_19c6f105dd0efded996f72ea7238228d))
; pre-typing for functions
;;; Fact-ids: 
(assert
 (! ;; def=Clase01.fst(82,14-85,54); use=Clase01.fst(82,14-85,54)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (implies
     (HasTypeFuel @u0 @x1 Tm_arrow_19c6f105dd0efded996f72ea7238228d)
     (is-Tm_arrow (PreType @x1)))
    :pattern ((HasTypeFuel @u0 @x1 Tm_arrow_19c6f105dd0efded996f72ea7238228d))
    :qid Clase01_pre_typing_Tm_arrow_19c6f105dd0efded996f72ea7238228d))
  :named Clase01_pre_typing_Tm_arrow_19c6f105dd0efded996f72ea7238228d))
; interpretation_Tm_arrow_19c6f105dd0efded996f72ea7238228d
;;; Fact-ids: 
(assert
 (! ;; def=Clase01.fst(82,14-85,54); use=Clase01.fst(82,14-85,54)
  (forall ((@x0 Term))
   (! (iff
     (HasTypeZ @x0 Tm_arrow_19c6f105dd0efded996f72ea7238228d)
     (and
      ;; def=Clase01.fst(82,14-85,54); use=Clase01.fst(82,14-85,54)
      (forall ((@x1 Term))
       (! (implies
         (HasType @x1 Tm_refine_c117e3dfa0913e9570f652c9d3f27f5b)
         (HasType (ApplyTT @x0 @x1) (Tm_refine_4f1d92a9a3f071e1fa3026ba94fce31c @x1)))
        :pattern ((ApplyTT @x0 @x1))
        :qid Clase01_interpretation_Tm_arrow_19c6f105dd0efded996f72ea7238228d.1))
      (IsTotFun @x0)))
    :pattern ((HasTypeZ @x0 Tm_arrow_19c6f105dd0efded996f72ea7238228d))
    :qid Clase01_interpretation_Tm_arrow_19c6f105dd0efded996f72ea7238228d))
  :named Clase01_interpretation_Tm_arrow_19c6f105dd0efded996f72ea7238228d))
(declare-fun Clase01.fib_@tok () Term)
; Name-token correspondence
;;; Fact-ids: 
(assert
 (! ;; def=Clase01.fst(82,8-82,12); use=Clase01.fst(82,8-82,12)
  (forall ((@x0 Term))
   (! (= (ApplyTT Clase01.fib_@tok @x0) (Clase01.fib_ @x0))
    :pattern ((ApplyTT Clase01.fib_@tok @x0))
    :qid token_correspondence_Clase01.fib_))
  :named token_correspondence_Clase01.fib_))
; function token typing
;;; Fact-ids: 
(assert
 (! ;; def=Clase01.fst(82,8-82,12); use=Clase01.fst(82,8-82,12)
  (forall ((@x0 Term))
   (! (and
     (NoHoist @x0 (HasType Clase01.fib_@tok Tm_arrow_19c6f105dd0efded996f72ea7238228d))
     ;; def=Clase01.fst(82,8-82,12); use=Clase01.fst(82,8-82,12)
     (forall ((@x1 Term))
      (! (= (ApplyTT Clase01.fib_@tok @x1) (Clase01.fib_ @x1))
       :pattern ((Clase01.fib_ @x1))
       :qid function_token_typing_Clase01.fib_.1)))
    :pattern ((ApplyTT @x0 Clase01.fib_@tok))
    :qid function_token_typing_Clase01.fib_))
  :named function_token_typing_Clase01.fib_))

; free var typing
;;; Fact-ids: 
(assert
 (! ;; def=Clase01.fst(82,8-82,12); use=Clase01.fst(82,8-82,12)
  (forall ((@x0 Term))
   (! (implies
     (HasType @x0 Tm_refine_c117e3dfa0913e9570f652c9d3f27f5b)
     (HasType (Clase01.fib_ @x0) (Tm_refine_4f1d92a9a3f071e1fa3026ba94fce31c @x0)))
    :pattern ((Clase01.fib_ @x0))
    :qid typing_Clase01.fib_))
  :named typing_Clase01.fib_))
(declare-fun label_6 () Bool)
(declare-fun label_5 () Bool)
(declare-fun label_4 () Bool)
(declare-fun label_3 () Bool)
(declare-fun label_2 () Bool)
(declare-fun label_1 () Bool)
(declare-fun Tm_refine_7a42f32a02c9d8ce0b30070f062fc0f8 () Term)
; refinement kinding
;;; Fact-ids: 
(assert
 (! (HasType Tm_refine_7a42f32a02c9d8ce0b30070f062fc0f8 Tm_type)
  :named refinement_kinding_Tm_refine_7a42f32a02c9d8ce0b30070f062fc0f8))
; refinement_interpretation
;;; Fact-ids: 
(assert
 (! ;; def=Clase01.fst(82,23-82,39); use=Clase01.fst(82,42-85,54)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 Tm_refine_7a42f32a02c9d8ce0b30070f062fc0f8)
     (and
      (HasTypeFuel @u0 @x1 Prims.int)
      ;; def=Clase01.fst(82,31-82,37); use=Clase01.fst(82,42-85,54)
      (>= (BoxInt_proj_0 @x1) (BoxInt_proj_0 x_ae567c2fb75be05905677af440075565_0))))
    :pattern ((HasTypeFuel @u0 @x1 Tm_refine_7a42f32a02c9d8ce0b30070f062fc0f8))
    :qid refinement_interpretation_Tm_refine_7a42f32a02c9d8ce0b30070f062fc0f8))
  :named refinement_interpretation_Tm_refine_7a42f32a02c9d8ce0b30070f062fc0f8))
; haseq for Tm_refine_7a42f32a02c9d8ce0b30070f062fc0f8
;;; Fact-ids: 
(assert
 (! (iff
   (Valid (Prims.hasEq Tm_refine_7a42f32a02c9d8ce0b30070f062fc0f8))
   (Valid (Prims.hasEq Prims.int)))
  :named haseqTm_refine_7a42f32a02c9d8ce0b30070f062fc0f8))


(declare-fun Tm_refine_14661f8e513c3c7ee26d003552553ce9 () Term)
; refinement kinding
;;; Fact-ids: 
(assert
 (! (HasType Tm_refine_14661f8e513c3c7ee26d003552553ce9 Tm_type)
  :named refinement_kinding_Tm_refine_14661f8e513c3c7ee26d003552553ce9))
; refinement_interpretation
;;; Fact-ids: 
(assert
 (! ;; def=Clase01.fst(82,23-82,39); use=Clase01.fst(82,42-85,54)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 Tm_refine_14661f8e513c3c7ee26d003552553ce9)
     (and
      (HasTypeFuel @u0 @x1 Prims.int)
      ;; def=Clase01.fst(82,31-82,37); use=Clase01.fst(82,42-85,54)
      (>=
       (BoxInt_proj_0 @x1)
       (BoxInt_proj_0 (Prims.op_Subtraction x_ae567c2fb75be05905677af440075565_0 (BoxInt 1))))))
    :pattern ((HasTypeFuel @u0 @x1 Tm_refine_14661f8e513c3c7ee26d003552553ce9))
    :qid refinement_interpretation_Tm_refine_14661f8e513c3c7ee26d003552553ce9))
  :named refinement_interpretation_Tm_refine_14661f8e513c3c7ee26d003552553ce9))
; haseq for Tm_refine_14661f8e513c3c7ee26d003552553ce9
;;; Fact-ids: 
(assert
 (! (iff
   (Valid (Prims.hasEq Tm_refine_14661f8e513c3c7ee26d003552553ce9))
   (Valid (Prims.hasEq Prims.int)))
  :named haseqTm_refine_14661f8e513c3c7ee26d003552553ce9))


(declare-fun Tm_refine_4e6f2c3480a93437e1fa5631dd134168 () Term)
; refinement kinding
;;; Fact-ids: 
(assert
 (! (HasType Tm_refine_4e6f2c3480a93437e1fa5631dd134168 Tm_type)
  :named refinement_kinding_Tm_refine_4e6f2c3480a93437e1fa5631dd134168))
; refinement_interpretation
;;; Fact-ids: 
(assert
 (! ;; def=Clase01.fst(82,23-82,39); use=Clase01.fst(82,42-85,54)
  (forall ((@u0 Fuel) (@x1 Term))
   (! (iff
     (HasTypeFuel @u0 @x1 Tm_refine_4e6f2c3480a93437e1fa5631dd134168)
     (and
      (HasTypeFuel @u0 @x1 Prims.int)
      ;; def=Clase01.fst(82,31-82,37); use=Clase01.fst(82,42-85,54)
      (>=
       (BoxInt_proj_0 @x1)
       (BoxInt_proj_0 (Prims.op_Subtraction x_ae567c2fb75be05905677af440075565_0 (BoxInt 2))))))
    :pattern ((HasTypeFuel @u0 @x1 Tm_refine_4e6f2c3480a93437e1fa5631dd134168))
    :qid refinement_interpretation_Tm_refine_4e6f2c3480a93437e1fa5631dd134168))
  :named refinement_interpretation_Tm_refine_4e6f2c3480a93437e1fa5631dd134168))
; haseq for Tm_refine_4e6f2c3480a93437e1fa5631dd134168
;;; Fact-ids: 
(assert
 (! (iff
   (Valid (Prims.hasEq Tm_refine_4e6f2c3480a93437e1fa5631dd134168))
   (Valid (Prims.hasEq Prims.int)))
  :named haseqTm_refine_4e6f2c3480a93437e1fa5631dd134168))



; Encoding query formula : forall (k: Prims.pure_post (y: Prims.int{y >= x})).
;   (forall (x: y: Prims.int{y >= x}). {:pattern Prims.guard_free (k x)} Prims.auto_squash (k x)) ==>
;   (x == 0 ==> 1 >= x) /\
;   (~(x = 0) ==>
;     (x == 1 ==> 1 >= x) /\
;     (~(x = 1) ==>
;       (forall (b: Prims.int).
;           x == b ==>
;           (forall (k: Prims.pure_post (y: Prims.int{y >= x})).
;               (forall (x: y: Prims.int{y >= x}). {:pattern Prims.guard_free (k x)}
;                   Prims.auto_squash (k x)) ==>
;               (x >= 0 == true ==>
;                 x - 1 << x /\
;                 (forall (return_val: x: Prims.int{x << x}).
;                     return_val == x - 1 ==>
;                     (forall (any_result: y: Prims.int{y >= x - 1}).
;                         Clase01.fib' (x - 1) == any_result ==>
;                         (forall (return_val: y: Prims.int{y >= x - 1}).
;                             return_val == Clase01.fib' (x - 1) ==>
;                             Clase01.fib' (x - 1) == return_val ==>
;                             x - 2 << x /\
;                             (forall (return_val: x: Prims.int{x << x}).
;                                 return_val == x - 2 ==>
;                                 (forall (any_result: y: Prims.int{y >= x - 2}).
;                                     Clase01.fib' (x - 2) == any_result ==>
;                                     (forall (return_val: y: Prims.int{y >= x - 2}).
;                                         return_val == Clase01.fib' (x - 2) ==>
;                                         Clase01.fib' (x - 2) == return_val ==>
;                                         (forall (any_result: Prims.int).
;                                             Clase01.fib' (x - 1) + Clase01.fib' (x - 2) ==
;                                             any_result ==>
;                                             Clase01.fib' (x - 1) + Clase01.fib' (x - 2) >= x)))))))) /\
;               (~(x >= 0 = true) ==> (forall (b: Prims.bool). x >= 0 == b ==> 1 >= x))))))
; Context: While encoding a query
; While typechecking the top-level declaration `let rec fib'`
(push) ;; push{0
; <fuel='2' ifuel='1'>
;;; Fact-ids: 
(assert (! (= MaxFuel (SFuel (SFuel ZFuel))) :named @MaxFuel_assumption))
;;; Fact-ids: 
(assert (! (= MaxIFuel (SFuel ZFuel)) :named @MaxIFuel_assumption))
; query
;;; Fact-ids: 
(assert
 (! (not
   (forall ((@x0 Term))
    (! (implies
      (and
       (HasType @x0 (Prims.pure_post Tm_refine_7a42f32a02c9d8ce0b30070f062fc0f8))
       ;; def=Prims.fst(410,27-410,88); use=Clase01.fst(82,42-85,54)
       (forall ((@x1 Term))
        (! ;; def=Prims.fst(410,84-410,87); use=Clase01.fst(82,42-85,54)
         (Valid
          ;; def=Prims.fst(410,84-410,87); use=Clase01.fst(82,42-85,54)
          (ApplyTT @x0 @x1))
         :pattern ((ApplyTT @x0 @x1))
         :qid @query.1)))
      ;; def=Prims.fst(397,2-397,39); use=Clase01.fst(82,42-85,54)
      (and
       (implies
        ;; def=Clase01.fst(82,14-83,5); use=Clase01.fst(82,48-83,5)
        (= x_ae567c2fb75be05905677af440075565_0 (BoxInt 0))
        ;; def=Clase01.fst(82,31-82,37); use=Clase01.fst(83,9-83,10)
        (or
         label_1
         ;; def=Clase01.fst(82,31-82,37); use=Clase01.fst(83,9-83,10)
         (>= (BoxInt_proj_0 (BoxInt 1)) (BoxInt_proj_0 x_ae567c2fb75be05905677af440075565_0))))
       (implies
        ;; def=Prims.fst(397,19-397,21); use=Clase01.fst(82,42-85,54)
        (not
         ;; def=Clase01.fst(82,14-83,5); use=Clase01.fst(82,48-83,5)
         (= x_ae567c2fb75be05905677af440075565_0 (BoxInt 0)))
        ;; def=Prims.fst(397,2-397,39); use=Clase01.fst(82,42-85,54)
        (and
         (implies
          ;; def=Clase01.fst(82,14-84,5); use=Clase01.fst(82,48-84,5)
          (= x_ae567c2fb75be05905677af440075565_0 (BoxInt 1))
          ;; def=Clase01.fst(82,31-82,37); use=Clase01.fst(84,9-84,10)
          (or
           label_2
           ;; def=Clase01.fst(82,31-82,37); use=Clase01.fst(84,9-84,10)
           (>= (BoxInt_proj_0 (BoxInt 1)) (BoxInt_proj_0 x_ae567c2fb75be05905677af440075565_0))))
         (implies
          ;; def=Prims.fst(397,19-397,21); use=Clase01.fst(82,42-85,54)
          (not
           ;; def=Clase01.fst(82,14-84,5); use=Clase01.fst(82,48-84,5)
           (= x_ae567c2fb75be05905677af440075565_0 (BoxInt 1)))
          ;; def=Prims.fst(421,99-421,120); use=Clase01.fst(82,42-85,54)
          (forall ((@x1 Term))
           (! (implies
             (and
              (HasType @x1 Prims.int)
              ;; def=Clase01.fst(82,14-85,5); use=Clase01.fst(82,48-85,5)
              (= x_ae567c2fb75be05905677af440075565_0 @x1))
             (forall ((@x2 Term))
              (! (implies
                (and
                 (HasType @x2 (Prims.pure_post Tm_refine_7a42f32a02c9d8ce0b30070f062fc0f8))
                 ;; def=Prims.fst(410,27-410,88); use=Clase01.fst(82,42-85,54)
                 (forall ((@x3 Term))
                  (! ;; def=Prims.fst(410,84-410,87); use=Clase01.fst(82,42-85,54)
                   (Valid
                    ;; def=Prims.fst(410,84-410,87); use=Clase01.fst(82,42-85,54)
                    (ApplyTT @x2 @x3))
                   :pattern ((ApplyTT @x2 @x3))
                   :qid @query.4)))
                ;; def=Prims.fst(397,2-397,39); use=Clase01.fst(82,42-85,54)
                (and
                 (implies
                  ;; def=Clase01.fst(85,12-85,18); use=Clase01.fst(85,12-85,18)
                  (=
                   (Prims.op_GreaterThanOrEqual x_ae567c2fb75be05905677af440075565_0 (BoxInt 0))
                   (BoxBool true))
                  ;; def=Prims.fst(467,77-467,89); use=Clase01.fst(82,42-85,54)
                  (and
                   ;; def=Clase01.fst(82,42-85,54); use=Clase01.fst(85,29-85,34)
                   (or
                    label_3
                    ;; def=Clase01.fst(82,42-85,54); use=Clase01.fst(85,29-85,34)
                    (Valid
                     ;; def=Clase01.fst(82,42-85,54); use=Clase01.fst(85,29-85,34)
                     (Prims.precedes
                      Prims.int
                      Prims.int
                      (Prims.op_Subtraction x_ae567c2fb75be05905677af440075565_0 (BoxInt 1))
                      x_ae567c2fb75be05905677af440075565_0)))
                   ;; def=Prims.fst(364,2-364,58); use=Clase01.fst(82,42-85,54)
                   (forall ((@x3 Term))
                    (! (implies
                      (and
                       (HasType @x3 Tm_refine_c117e3dfa0913e9570f652c9d3f27f5b)
                       ;; def=Prims.fst(364,26-364,41); use=Clase01.fst(82,42-85,54)
                       (= @x3 (Prims.op_Subtraction x_ae567c2fb75be05905677af440075565_0 (BoxInt 1))))
                      ;; def=Prims.fst(459,66-459,102); use=Clase01.fst(82,42-85,54)
                      (forall ((@x4 Term))
                       (! (implies
                         (and
                          (HasType @x4 Tm_refine_14661f8e513c3c7ee26d003552553ce9)
                          ;; def=Clase01.fst(82,23-85,34); use=Clase01.fst(85,24-85,34)
                          (=
                           (Clase01.fib_
                            (Prims.op_Subtraction x_ae567c2fb75be05905677af440075565_0 (BoxInt 1)))
                           @x4))
                         ;; def=Prims.fst(364,2-364,58); use=Clase01.fst(82,42-85,54)
                         (forall ((@x5 Term))
                          (! (implies
                            (and
                             (HasType @x5 Tm_refine_14661f8e513c3c7ee26d003552553ce9)
                             ;; def=Prims.fst(364,26-364,41); use=Clase01.fst(82,42-85,54)
                             (=
                              @x5
                              (Clase01.fib_
                               (Prims.op_Subtraction x_ae567c2fb75be05905677af440075565_0 (BoxInt 1))))
                             ;; def=dummy(0,0-0,0); use=Clase01.fst(82,42-85,54)
                             (=
                              (Clase01.fib_
                               (Prims.op_Subtraction x_ae567c2fb75be05905677af440075565_0 (BoxInt 1)))
                              @x5))
                            ;; def=Prims.fst(467,77-467,89); use=Clase01.fst(82,42-85,54)
                            (and
                             ;; def=Clase01.fst(82,42-85,54); use=Clase01.fst(85,42-85,47)
                             (or
                              label_4
                              ;; def=Clase01.fst(82,42-85,54); use=Clase01.fst(85,42-85,47)
                              (Valid
                               ;; def=Clase01.fst(82,42-85,54); use=Clase01.fst(85,42-85,47)
                               (Prims.precedes
                                Prims.int
                                Prims.int
                                (Prims.op_Subtraction
                                 x_ae567c2fb75be05905677af440075565_0
                                 (BoxInt 2))
                                x_ae567c2fb75be05905677af440075565_0)))
                             ;; def=Prims.fst(364,2-364,58); use=Clase01.fst(82,42-85,54)
                             (forall ((@x6 Term))
                              (! (implies
                                (and
                                 (HasType @x6 Tm_refine_c117e3dfa0913e9570f652c9d3f27f5b)
                                 ;; def=Prims.fst(364,26-364,41); use=Clase01.fst(82,42-85,54)
                                 (=
                                  @x6
                                  (Prims.op_Subtraction
                                   x_ae567c2fb75be05905677af440075565_0
                                   (BoxInt 2))))
                                ;; def=Prims.fst(459,66-459,102); use=Clase01.fst(82,42-85,54)
                                (forall ((@x7 Term))
                                 (! (implies
                                   (and
                                    (HasType @x7 Tm_refine_4e6f2c3480a93437e1fa5631dd134168)
                                    ;; def=Clase01.fst(82,23-85,47); use=Clase01.fst(85,37-85,47)
                                    (=
                                     (Clase01.fib_
                                      (Prims.op_Subtraction
                                       x_ae567c2fb75be05905677af440075565_0
                                       (BoxInt 2)))
                                     @x7))
                                   ;; def=Prims.fst(364,2-364,58); use=Clase01.fst(82,42-85,54)
                                   (forall ((@x8 Term))
                                    (! (implies
                                      (and
                                       (HasType @x8 Tm_refine_4e6f2c3480a93437e1fa5631dd134168)
                                       ;; def=Prims.fst(364,26-364,41); use=Clase01.fst(82,42-85,54)
                                       (=
                                        @x8
                                        (Clase01.fib_
                                         (Prims.op_Subtraction
                                          x_ae567c2fb75be05905677af440075565_0
                                          (BoxInt 2))))
                                       ;; def=dummy(0,0-0,0); use=Clase01.fst(82,42-85,54)
                                       (=
                                        (Clase01.fib_
                                         (Prims.op_Subtraction
                                          x_ae567c2fb75be05905677af440075565_0
                                          (BoxInt 2)))
                                        @x8))
                                      ;; def=Prims.fst(459,66-459,102); use=Clase01.fst(82,42-85,54)
                                      (forall ((@x9 Term))
                                       (! (implies
                                         (and
                                          (HasType @x9 Prims.int)
                                          ;; def=Clase01.fst(82,23-85,47); use=Clase01.fst(82,42-85,54)
                                          (=
                                           (Prims.op_Addition
                                            (Clase01.fib_
                                             (Prims.op_Subtraction
                                              x_ae567c2fb75be05905677af440075565_0
                                              (BoxInt 1)))
                                            (Clase01.fib_
                                             (Prims.op_Subtraction
                                              x_ae567c2fb75be05905677af440075565_0
                                              (BoxInt 2))))
                                           @x9))
                                         ;; def=Clase01.fst(82,31-82,37); use=Clase01.fst(85,24-85,47)
                                         (or
                                          label_5
                                          ;; def=Clase01.fst(82,31-82,37); use=Clase01.fst(85,24-85,47)
                                          (>=
                                           (BoxInt_proj_0
                                            (Prims.op_Addition
                                             (Clase01.fib_
                                              (Prims.op_Subtraction
                                               x_ae567c2fb75be05905677af440075565_0
                                               (BoxInt 1)))
                                             (Clase01.fib_
                                              (Prims.op_Subtraction
                                               x_ae567c2fb75be05905677af440075565_0
                                               (BoxInt 2)))))
                                           (BoxInt_proj_0 x_ae567c2fb75be05905677af440075565_0))))
                                        :qid @query.11)))
                                     :qid @query.10)))
                                  :qid @query.9)))
                               :qid @query.8))))
                           :qid @query.7)))
                        :qid @query.6)))
                     :qid @query.5))))
                 (implies
                  ;; def=Prims.fst(397,19-397,21); use=Clase01.fst(82,42-85,54)
                  (not
                   ;; def=Clase01.fst(85,12-85,18); use=Clase01.fst(85,12-85,18)
                   (=
                    (Prims.op_GreaterThanOrEqual x_ae567c2fb75be05905677af440075565_0 (BoxInt 0))
                    (BoxBool true)))
                  ;; def=Prims.fst(421,99-421,120); use=Clase01.fst(82,42-85,54)
                  (forall ((@x3 Term))
                   (! (implies
                     (and
                      (HasType @x3 Prims.bool)
                      ;; def=Clase01.fst(85,12-85,54); use=Clase01.fst(85,12-85,54)
                      (=
                       (Prims.op_GreaterThanOrEqual x_ae567c2fb75be05905677af440075565_0 (BoxInt 0))
                       @x3))
                     ;; def=Clase01.fst(82,31-82,37); use=Clase01.fst(85,53-85,54)
                     (or
                      label_6
                      ;; def=Clase01.fst(82,31-82,37); use=Clase01.fst(85,53-85,54)
                      (>=
                       (BoxInt_proj_0 (BoxInt 1))
                       (BoxInt_proj_0 x_ae567c2fb75be05905677af440075565_0))))
                    :qid @query.12)))))
               :qid @query.3)))
            :qid @query.2)))))))
     :qid @query)))
  :named @query))
(set-option :rlimit 2723280)
(echo "<initial_stats>")
(echo "<statistics>") (get-info :all-statistics) (echo "</statistics>")
(echo "</initial_stats>")
(echo "<result>")
(check-sat)
(echo "</result>")
(set-option :rlimit 0)
(echo "<reason-unknown>") (get-info :reason-unknown) (echo "</reason-unknown>")
(echo "<labels>")
(echo "label_6")
(eval label_6)
(echo "label_5")
(eval label_5)
(echo "label_4")
(eval label_4)
(echo "label_3")
(eval label_3)
(echo "label_2")
(eval label_2)
(echo "label_1")
(eval label_1)
(echo "</labels>")
(echo "Done!")
(pop) ;; 0}pop

; QUERY ID: (Clase01.fib', 1)
; STATUS: unknown because (incomplete quantifiers)
; Z3 invocation started by F*
; F* version: 2025.08.07~dev -- commit hash: unset
; Z3 version (according to F*): 4.8.5

(push) ;; push{0
; <fuel='2' ifuel='2'>
;;; Fact-ids: 
(assert (! (= MaxFuel (SFuel (SFuel ZFuel))) :named @MaxFuel_assumption))
;;; Fact-ids: 
(assert (! (= MaxIFuel (SFuel (SFuel ZFuel))) :named @MaxIFuel_assumption))
; query
;;; Fact-ids: 
(assert
 (! (not
   (forall ((@x0 Term))
    (! (implies
      (and
       (HasType @x0 (Prims.pure_post Tm_refine_7a42f32a02c9d8ce0b30070f062fc0f8))
       ;; def=Prims.fst(410,27-410,88); use=Clase01.fst(82,42-85,54)
       (forall ((@x1 Term))
        (! ;; def=Prims.fst(410,84-410,87); use=Clase01.fst(82,42-85,54)
         (Valid
          ;; def=Prims.fst(410,84-410,87); use=Clase01.fst(82,42-85,54)
          (ApplyTT @x0 @x1))
         :pattern ((ApplyTT @x0 @x1))
         :qid @query.1)))
      ;; def=Prims.fst(397,2-397,39); use=Clase01.fst(82,42-85,54)
      (and
       (implies
        ;; def=Clase01.fst(82,14-83,5); use=Clase01.fst(82,48-83,5)
        (= x_ae567c2fb75be05905677af440075565_0 (BoxInt 0))
        ;; def=Clase01.fst(82,31-82,37); use=Clase01.fst(83,9-83,10)
        (or
         label_1
         ;; def=Clase01.fst(82,31-82,37); use=Clase01.fst(83,9-83,10)
         (>= (BoxInt_proj_0 (BoxInt 1)) (BoxInt_proj_0 x_ae567c2fb75be05905677af440075565_0))))
       (implies
        ;; def=Prims.fst(397,19-397,21); use=Clase01.fst(82,42-85,54)
        (not
         ;; def=Clase01.fst(82,14-83,5); use=Clase01.fst(82,48-83,5)
         (= x_ae567c2fb75be05905677af440075565_0 (BoxInt 0)))
        ;; def=Prims.fst(397,2-397,39); use=Clase01.fst(82,42-85,54)
        (and
         (implies
          ;; def=Clase01.fst(82,14-84,5); use=Clase01.fst(82,48-84,5)
          (= x_ae567c2fb75be05905677af440075565_0 (BoxInt 1))
          ;; def=Clase01.fst(82,31-82,37); use=Clase01.fst(84,9-84,10)
          (or
           label_2
           ;; def=Clase01.fst(82,31-82,37); use=Clase01.fst(84,9-84,10)
           (>= (BoxInt_proj_0 (BoxInt 1)) (BoxInt_proj_0 x_ae567c2fb75be05905677af440075565_0))))
         (implies
          ;; def=Prims.fst(397,19-397,21); use=Clase01.fst(82,42-85,54)
          (not
           ;; def=Clase01.fst(82,14-84,5); use=Clase01.fst(82,48-84,5)
           (= x_ae567c2fb75be05905677af440075565_0 (BoxInt 1)))
          ;; def=Prims.fst(421,99-421,120); use=Clase01.fst(82,42-85,54)
          (forall ((@x1 Term))
           (! (implies
             (and
              (HasType @x1 Prims.int)
              ;; def=Clase01.fst(82,14-85,5); use=Clase01.fst(82,48-85,5)
              (= x_ae567c2fb75be05905677af440075565_0 @x1))
             (forall ((@x2 Term))
              (! (implies
                (and
                 (HasType @x2 (Prims.pure_post Tm_refine_7a42f32a02c9d8ce0b30070f062fc0f8))
                 ;; def=Prims.fst(410,27-410,88); use=Clase01.fst(82,42-85,54)
                 (forall ((@x3 Term))
                  (! ;; def=Prims.fst(410,84-410,87); use=Clase01.fst(82,42-85,54)
                   (Valid
                    ;; def=Prims.fst(410,84-410,87); use=Clase01.fst(82,42-85,54)
                    (ApplyTT @x2 @x3))
                   :pattern ((ApplyTT @x2 @x3))
                   :qid @query.4)))
                ;; def=Prims.fst(397,2-397,39); use=Clase01.fst(82,42-85,54)
                (and
                 (implies
                  ;; def=Clase01.fst(85,12-85,18); use=Clase01.fst(85,12-85,18)
                  (=
                   (Prims.op_GreaterThanOrEqual x_ae567c2fb75be05905677af440075565_0 (BoxInt 0))
                   (BoxBool true))
                  ;; def=Prims.fst(467,77-467,89); use=Clase01.fst(82,42-85,54)
                  (and
                   ;; def=Clase01.fst(82,42-85,54); use=Clase01.fst(85,29-85,34)
                   (or
                    label_3
                    ;; def=Clase01.fst(82,42-85,54); use=Clase01.fst(85,29-85,34)
                    (Valid
                     ;; def=Clase01.fst(82,42-85,54); use=Clase01.fst(85,29-85,34)
                     (Prims.precedes
                      Prims.int
                      Prims.int
                      (Prims.op_Subtraction x_ae567c2fb75be05905677af440075565_0 (BoxInt 1))
                      x_ae567c2fb75be05905677af440075565_0)))
                   ;; def=Prims.fst(364,2-364,58); use=Clase01.fst(82,42-85,54)
                   (forall ((@x3 Term))
                    (! (implies
                      (and
                       (HasType @x3 Tm_refine_c117e3dfa0913e9570f652c9d3f27f5b)
                       ;; def=Prims.fst(364,26-364,41); use=Clase01.fst(82,42-85,54)
                       (= @x3 (Prims.op_Subtraction x_ae567c2fb75be05905677af440075565_0 (BoxInt 1))))
                      ;; def=Prims.fst(459,66-459,102); use=Clase01.fst(82,42-85,54)
                      (forall ((@x4 Term))
                       (! (implies
                         (and
                          (HasType @x4 Tm_refine_14661f8e513c3c7ee26d003552553ce9)
                          ;; def=Clase01.fst(82,23-85,34); use=Clase01.fst(85,24-85,34)
                          (=
                           (Clase01.fib_
                            (Prims.op_Subtraction x_ae567c2fb75be05905677af440075565_0 (BoxInt 1)))
                           @x4))
                         ;; def=Prims.fst(364,2-364,58); use=Clase01.fst(82,42-85,54)
                         (forall ((@x5 Term))
                          (! (implies
                            (and
                             (HasType @x5 Tm_refine_14661f8e513c3c7ee26d003552553ce9)
                             ;; def=Prims.fst(364,26-364,41); use=Clase01.fst(82,42-85,54)
                             (=
                              @x5
                              (Clase01.fib_
                               (Prims.op_Subtraction x_ae567c2fb75be05905677af440075565_0 (BoxInt 1))))
                             ;; def=dummy(0,0-0,0); use=Clase01.fst(82,42-85,54)
                             (=
                              (Clase01.fib_
                               (Prims.op_Subtraction x_ae567c2fb75be05905677af440075565_0 (BoxInt 1)))
                              @x5))
                            ;; def=Prims.fst(467,77-467,89); use=Clase01.fst(82,42-85,54)
                            (and
                             ;; def=Clase01.fst(82,42-85,54); use=Clase01.fst(85,42-85,47)
                             (or
                              label_4
                              ;; def=Clase01.fst(82,42-85,54); use=Clase01.fst(85,42-85,47)
                              (Valid
                               ;; def=Clase01.fst(82,42-85,54); use=Clase01.fst(85,42-85,47)
                               (Prims.precedes
                                Prims.int
                                Prims.int
                                (Prims.op_Subtraction
                                 x_ae567c2fb75be05905677af440075565_0
                                 (BoxInt 2))
                                x_ae567c2fb75be05905677af440075565_0)))
                             ;; def=Prims.fst(364,2-364,58); use=Clase01.fst(82,42-85,54)
                             (forall ((@x6 Term))
                              (! (implies
                                (and
                                 (HasType @x6 Tm_refine_c117e3dfa0913e9570f652c9d3f27f5b)
                                 ;; def=Prims.fst(364,26-364,41); use=Clase01.fst(82,42-85,54)
                                 (=
                                  @x6
                                  (Prims.op_Subtraction
                                   x_ae567c2fb75be05905677af440075565_0
                                   (BoxInt 2))))
                                ;; def=Prims.fst(459,66-459,102); use=Clase01.fst(82,42-85,54)
                                (forall ((@x7 Term))
                                 (! (implies
                                   (and
                                    (HasType @x7 Tm_refine_4e6f2c3480a93437e1fa5631dd134168)
                                    ;; def=Clase01.fst(82,23-85,47); use=Clase01.fst(85,37-85,47)
                                    (=
                                     (Clase01.fib_
                                      (Prims.op_Subtraction
                                       x_ae567c2fb75be05905677af440075565_0
                                       (BoxInt 2)))
                                     @x7))
                                   ;; def=Prims.fst(364,2-364,58); use=Clase01.fst(82,42-85,54)
                                   (forall ((@x8 Term))
                                    (! (implies
                                      (and
                                       (HasType @x8 Tm_refine_4e6f2c3480a93437e1fa5631dd134168)
                                       ;; def=Prims.fst(364,26-364,41); use=Clase01.fst(82,42-85,54)
                                       (=
                                        @x8
                                        (Clase01.fib_
                                         (Prims.op_Subtraction
                                          x_ae567c2fb75be05905677af440075565_0
                                          (BoxInt 2))))
                                       ;; def=dummy(0,0-0,0); use=Clase01.fst(82,42-85,54)
                                       (=
                                        (Clase01.fib_
                                         (Prims.op_Subtraction
                                          x_ae567c2fb75be05905677af440075565_0
                                          (BoxInt 2)))
                                        @x8))
                                      ;; def=Prims.fst(459,66-459,102); use=Clase01.fst(82,42-85,54)
                                      (forall ((@x9 Term))
                                       (! (implies
                                         (and
                                          (HasType @x9 Prims.int)
                                          ;; def=Clase01.fst(82,23-85,47); use=Clase01.fst(82,42-85,54)
                                          (=
                                           (Prims.op_Addition
                                            (Clase01.fib_
                                             (Prims.op_Subtraction
                                              x_ae567c2fb75be05905677af440075565_0
                                              (BoxInt 1)))
                                            (Clase01.fib_
                                             (Prims.op_Subtraction
                                              x_ae567c2fb75be05905677af440075565_0
                                              (BoxInt 2))))
                                           @x9))
                                         ;; def=Clase01.fst(82,31-82,37); use=Clase01.fst(85,24-85,47)
                                         (or
                                          label_5
                                          ;; def=Clase01.fst(82,31-82,37); use=Clase01.fst(85,24-85,47)
                                          (>=
                                           (BoxInt_proj_0
                                            (Prims.op_Addition
                                             (Clase01.fib_
                                              (Prims.op_Subtraction
                                               x_ae567c2fb75be05905677af440075565_0
                                               (BoxInt 1)))
                                             (Clase01.fib_
                                              (Prims.op_Subtraction
                                               x_ae567c2fb75be05905677af440075565_0
                                               (BoxInt 2)))))
                                           (BoxInt_proj_0 x_ae567c2fb75be05905677af440075565_0))))
                                        :qid @query.11)))
                                     :qid @query.10)))
                                  :qid @query.9)))
                               :qid @query.8))))
                           :qid @query.7)))
                        :qid @query.6)))
                     :qid @query.5))))
                 (implies
                  ;; def=Prims.fst(397,19-397,21); use=Clase01.fst(82,42-85,54)
                  (not
                   ;; def=Clase01.fst(85,12-85,18); use=Clase01.fst(85,12-85,18)
                   (=
                    (Prims.op_GreaterThanOrEqual x_ae567c2fb75be05905677af440075565_0 (BoxInt 0))
                    (BoxBool true)))
                  ;; def=Prims.fst(421,99-421,120); use=Clase01.fst(82,42-85,54)
                  (forall ((@x3 Term))
                   (! (implies
                     (and
                      (HasType @x3 Prims.bool)
                      ;; def=Clase01.fst(85,12-85,54); use=Clase01.fst(85,12-85,54)
                      (=
                       (Prims.op_GreaterThanOrEqual x_ae567c2fb75be05905677af440075565_0 (BoxInt 0))
                       @x3))
                     ;; def=Clase01.fst(82,31-82,37); use=Clase01.fst(85,53-85,54)
                     (or
                      label_6
                      ;; def=Clase01.fst(82,31-82,37); use=Clase01.fst(85,53-85,54)
                      (>=
                       (BoxInt_proj_0 (BoxInt 1))
                       (BoxInt_proj_0 x_ae567c2fb75be05905677af440075565_0))))
                    :qid @query.12)))))
               :qid @query.3)))
            :qid @query.2)))))))
     :qid @query)))
  :named @query))
(set-option :rlimit 2723280)
(echo "<initial_stats>")
(echo "<statistics>") (get-info :all-statistics) (echo "</statistics>")
(echo "</initial_stats>")
(echo "<result>")
(check-sat)
(echo "</result>")
(set-option :rlimit 0)
(echo "<reason-unknown>") (get-info :reason-unknown) (echo "</reason-unknown>")
(echo "<labels>")
(echo "label_6")
(eval label_6)
(echo "label_5")
(eval label_5)
(echo "label_4")
(eval label_4)
(echo "label_3")
(eval label_3)
(echo "label_2")
(eval label_2)
(echo "label_1")
(eval label_1)
(echo "</labels>")
(echo "Done!")
(pop) ;; 0}pop

; QUERY ID: (Clase01.fib', 1)
; STATUS: unknown because (incomplete quantifiers)
; Z3 invocation started by F*
; F* version: 2025.08.07~dev -- commit hash: unset
; Z3 version (according to F*): 4.8.5

(push) ;; push{0
; <fuel='4' ifuel='2'>
;;; Fact-ids: 
(assert
 (! (= MaxFuel (SFuel (SFuel (SFuel (SFuel ZFuel))))) :named @MaxFuel_assumption))
;;; Fact-ids: 
(assert (! (= MaxIFuel (SFuel (SFuel ZFuel))) :named @MaxIFuel_assumption))
; query
;;; Fact-ids: 
(assert
 (! (not
   (forall ((@x0 Term))
    (! (implies
      (and
       (HasType @x0 (Prims.pure_post Tm_refine_7a42f32a02c9d8ce0b30070f062fc0f8))
       ;; def=Prims.fst(410,27-410,88); use=Clase01.fst(82,42-85,54)
       (forall ((@x1 Term))
        (! ;; def=Prims.fst(410,84-410,87); use=Clase01.fst(82,42-85,54)
         (Valid
          ;; def=Prims.fst(410,84-410,87); use=Clase01.fst(82,42-85,54)
          (ApplyTT @x0 @x1))
         :pattern ((ApplyTT @x0 @x1))
         :qid @query.1)))
      ;; def=Prims.fst(397,2-397,39); use=Clase01.fst(82,42-85,54)
      (and
       (implies
        ;; def=Clase01.fst(82,14-83,5); use=Clase01.fst(82,48-83,5)
        (= x_ae567c2fb75be05905677af440075565_0 (BoxInt 0))
        ;; def=Clase01.fst(82,31-82,37); use=Clase01.fst(83,9-83,10)
        (or
         label_1
         ;; def=Clase01.fst(82,31-82,37); use=Clase01.fst(83,9-83,10)
         (>= (BoxInt_proj_0 (BoxInt 1)) (BoxInt_proj_0 x_ae567c2fb75be05905677af440075565_0))))
       (implies
        ;; def=Prims.fst(397,19-397,21); use=Clase01.fst(82,42-85,54)
        (not
         ;; def=Clase01.fst(82,14-83,5); use=Clase01.fst(82,48-83,5)
         (= x_ae567c2fb75be05905677af440075565_0 (BoxInt 0)))
        ;; def=Prims.fst(397,2-397,39); use=Clase01.fst(82,42-85,54)
        (and
         (implies
          ;; def=Clase01.fst(82,14-84,5); use=Clase01.fst(82,48-84,5)
          (= x_ae567c2fb75be05905677af440075565_0 (BoxInt 1))
          ;; def=Clase01.fst(82,31-82,37); use=Clase01.fst(84,9-84,10)
          (or
           label_2
           ;; def=Clase01.fst(82,31-82,37); use=Clase01.fst(84,9-84,10)
           (>= (BoxInt_proj_0 (BoxInt 1)) (BoxInt_proj_0 x_ae567c2fb75be05905677af440075565_0))))
         (implies
          ;; def=Prims.fst(397,19-397,21); use=Clase01.fst(82,42-85,54)
          (not
           ;; def=Clase01.fst(82,14-84,5); use=Clase01.fst(82,48-84,5)
           (= x_ae567c2fb75be05905677af440075565_0 (BoxInt 1)))
          ;; def=Prims.fst(421,99-421,120); use=Clase01.fst(82,42-85,54)
          (forall ((@x1 Term))
           (! (implies
             (and
              (HasType @x1 Prims.int)
              ;; def=Clase01.fst(82,14-85,5); use=Clase01.fst(82,48-85,5)
              (= x_ae567c2fb75be05905677af440075565_0 @x1))
             (forall ((@x2 Term))
              (! (implies
                (and
                 (HasType @x2 (Prims.pure_post Tm_refine_7a42f32a02c9d8ce0b30070f062fc0f8))
                 ;; def=Prims.fst(410,27-410,88); use=Clase01.fst(82,42-85,54)
                 (forall ((@x3 Term))
                  (! ;; def=Prims.fst(410,84-410,87); use=Clase01.fst(82,42-85,54)
                   (Valid
                    ;; def=Prims.fst(410,84-410,87); use=Clase01.fst(82,42-85,54)
                    (ApplyTT @x2 @x3))
                   :pattern ((ApplyTT @x2 @x3))
                   :qid @query.4)))
                ;; def=Prims.fst(397,2-397,39); use=Clase01.fst(82,42-85,54)
                (and
                 (implies
                  ;; def=Clase01.fst(85,12-85,18); use=Clase01.fst(85,12-85,18)
                  (=
                   (Prims.op_GreaterThanOrEqual x_ae567c2fb75be05905677af440075565_0 (BoxInt 0))
                   (BoxBool true))
                  ;; def=Prims.fst(467,77-467,89); use=Clase01.fst(82,42-85,54)
                  (and
                   ;; def=Clase01.fst(82,42-85,54); use=Clase01.fst(85,29-85,34)
                   (or
                    label_3
                    ;; def=Clase01.fst(82,42-85,54); use=Clase01.fst(85,29-85,34)
                    (Valid
                     ;; def=Clase01.fst(82,42-85,54); use=Clase01.fst(85,29-85,34)
                     (Prims.precedes
                      Prims.int
                      Prims.int
                      (Prims.op_Subtraction x_ae567c2fb75be05905677af440075565_0 (BoxInt 1))
                      x_ae567c2fb75be05905677af440075565_0)))
                   ;; def=Prims.fst(364,2-364,58); use=Clase01.fst(82,42-85,54)
                   (forall ((@x3 Term))
                    (! (implies
                      (and
                       (HasType @x3 Tm_refine_c117e3dfa0913e9570f652c9d3f27f5b)
                       ;; def=Prims.fst(364,26-364,41); use=Clase01.fst(82,42-85,54)
                       (= @x3 (Prims.op_Subtraction x_ae567c2fb75be05905677af440075565_0 (BoxInt 1))))
                      ;; def=Prims.fst(459,66-459,102); use=Clase01.fst(82,42-85,54)
                      (forall ((@x4 Term))
                       (! (implies
                         (and
                          (HasType @x4 Tm_refine_14661f8e513c3c7ee26d003552553ce9)
                          ;; def=Clase01.fst(82,23-85,34); use=Clase01.fst(85,24-85,34)
                          (=
                           (Clase01.fib_
                            (Prims.op_Subtraction x_ae567c2fb75be05905677af440075565_0 (BoxInt 1)))
                           @x4))
                         ;; def=Prims.fst(364,2-364,58); use=Clase01.fst(82,42-85,54)
                         (forall ((@x5 Term))
                          (! (implies
                            (and
                             (HasType @x5 Tm_refine_14661f8e513c3c7ee26d003552553ce9)
                             ;; def=Prims.fst(364,26-364,41); use=Clase01.fst(82,42-85,54)
                             (=
                              @x5
                              (Clase01.fib_
                               (Prims.op_Subtraction x_ae567c2fb75be05905677af440075565_0 (BoxInt 1))))
                             ;; def=dummy(0,0-0,0); use=Clase01.fst(82,42-85,54)
                             (=
                              (Clase01.fib_
                               (Prims.op_Subtraction x_ae567c2fb75be05905677af440075565_0 (BoxInt 1)))
                              @x5))
                            ;; def=Prims.fst(467,77-467,89); use=Clase01.fst(82,42-85,54)
                            (and
                             ;; def=Clase01.fst(82,42-85,54); use=Clase01.fst(85,42-85,47)
                             (or
                              label_4
                              ;; def=Clase01.fst(82,42-85,54); use=Clase01.fst(85,42-85,47)
                              (Valid
                               ;; def=Clase01.fst(82,42-85,54); use=Clase01.fst(85,42-85,47)
                               (Prims.precedes
                                Prims.int
                                Prims.int
                                (Prims.op_Subtraction
                                 x_ae567c2fb75be05905677af440075565_0
                                 (BoxInt 2))
                                x_ae567c2fb75be05905677af440075565_0)))
                             ;; def=Prims.fst(364,2-364,58); use=Clase01.fst(82,42-85,54)
                             (forall ((@x6 Term))
                              (! (implies
                                (and
                                 (HasType @x6 Tm_refine_c117e3dfa0913e9570f652c9d3f27f5b)
                                 ;; def=Prims.fst(364,26-364,41); use=Clase01.fst(82,42-85,54)
                                 (=
                                  @x6
                                  (Prims.op_Subtraction
                                   x_ae567c2fb75be05905677af440075565_0
                                   (BoxInt 2))))
                                ;; def=Prims.fst(459,66-459,102); use=Clase01.fst(82,42-85,54)
                                (forall ((@x7 Term))
                                 (! (implies
                                   (and
                                    (HasType @x7 Tm_refine_4e6f2c3480a93437e1fa5631dd134168)
                                    ;; def=Clase01.fst(82,23-85,47); use=Clase01.fst(85,37-85,47)
                                    (=
                                     (Clase01.fib_
                                      (Prims.op_Subtraction
                                       x_ae567c2fb75be05905677af440075565_0
                                       (BoxInt 2)))
                                     @x7))
                                   ;; def=Prims.fst(364,2-364,58); use=Clase01.fst(82,42-85,54)
                                   (forall ((@x8 Term))
                                    (! (implies
                                      (and
                                       (HasType @x8 Tm_refine_4e6f2c3480a93437e1fa5631dd134168)
                                       ;; def=Prims.fst(364,26-364,41); use=Clase01.fst(82,42-85,54)
                                       (=
                                        @x8
                                        (Clase01.fib_
                                         (Prims.op_Subtraction
                                          x_ae567c2fb75be05905677af440075565_0
                                          (BoxInt 2))))
                                       ;; def=dummy(0,0-0,0); use=Clase01.fst(82,42-85,54)
                                       (=
                                        (Clase01.fib_
                                         (Prims.op_Subtraction
                                          x_ae567c2fb75be05905677af440075565_0
                                          (BoxInt 2)))
                                        @x8))
                                      ;; def=Prims.fst(459,66-459,102); use=Clase01.fst(82,42-85,54)
                                      (forall ((@x9 Term))
                                       (! (implies
                                         (and
                                          (HasType @x9 Prims.int)
                                          ;; def=Clase01.fst(82,23-85,47); use=Clase01.fst(82,42-85,54)
                                          (=
                                           (Prims.op_Addition
                                            (Clase01.fib_
                                             (Prims.op_Subtraction
                                              x_ae567c2fb75be05905677af440075565_0
                                              (BoxInt 1)))
                                            (Clase01.fib_
                                             (Prims.op_Subtraction
                                              x_ae567c2fb75be05905677af440075565_0
                                              (BoxInt 2))))
                                           @x9))
                                         ;; def=Clase01.fst(82,31-82,37); use=Clase01.fst(85,24-85,47)
                                         (or
                                          label_5
                                          ;; def=Clase01.fst(82,31-82,37); use=Clase01.fst(85,24-85,47)
                                          (>=
                                           (BoxInt_proj_0
                                            (Prims.op_Addition
                                             (Clase01.fib_
                                              (Prims.op_Subtraction
                                               x_ae567c2fb75be05905677af440075565_0
                                               (BoxInt 1)))
                                             (Clase01.fib_
                                              (Prims.op_Subtraction
                                               x_ae567c2fb75be05905677af440075565_0
                                               (BoxInt 2)))))
                                           (BoxInt_proj_0 x_ae567c2fb75be05905677af440075565_0))))
                                        :qid @query.11)))
                                     :qid @query.10)))
                                  :qid @query.9)))
                               :qid @query.8))))
                           :qid @query.7)))
                        :qid @query.6)))
                     :qid @query.5))))
                 (implies
                  ;; def=Prims.fst(397,19-397,21); use=Clase01.fst(82,42-85,54)
                  (not
                   ;; def=Clase01.fst(85,12-85,18); use=Clase01.fst(85,12-85,18)
                   (=
                    (Prims.op_GreaterThanOrEqual x_ae567c2fb75be05905677af440075565_0 (BoxInt 0))
                    (BoxBool true)))
                  ;; def=Prims.fst(421,99-421,120); use=Clase01.fst(82,42-85,54)
                  (forall ((@x3 Term))
                   (! (implies
                     (and
                      (HasType @x3 Prims.bool)
                      ;; def=Clase01.fst(85,12-85,54); use=Clase01.fst(85,12-85,54)
                      (=
                       (Prims.op_GreaterThanOrEqual x_ae567c2fb75be05905677af440075565_0 (BoxInt 0))
                       @x3))
                     ;; def=Clase01.fst(82,31-82,37); use=Clase01.fst(85,53-85,54)
                     (or
                      label_6
                      ;; def=Clase01.fst(82,31-82,37); use=Clase01.fst(85,53-85,54)
                      (>=
                       (BoxInt_proj_0 (BoxInt 1))
                       (BoxInt_proj_0 x_ae567c2fb75be05905677af440075565_0))))
                    :qid @query.12)))))
               :qid @query.3)))
            :qid @query.2)))))))
     :qid @query)))
  :named @query))
(set-option :rlimit 2723280)
(echo "<initial_stats>")
(echo "<statistics>") (get-info :all-statistics) (echo "</statistics>")
(echo "</initial_stats>")
(echo "<result>")
(check-sat)
(echo "</result>")
(set-option :rlimit 0)
(echo "<reason-unknown>") (get-info :reason-unknown) (echo "</reason-unknown>")
(echo "<labels>")
(echo "label_6")
(eval label_6)
(echo "label_5")
(eval label_5)
(echo "label_4")
(eval label_4)
(echo "label_3")
(eval label_3)
(echo "label_2")
(eval label_2)
(echo "label_1")
(eval label_1)
(echo "</labels>")
(echo "Done!")
(pop) ;; 0}pop

; QUERY ID: (Clase01.fib', 1)
; STATUS: unknown because (incomplete quantifiers)
; Z3 invocation started by F*
; F* version: 2025.08.07~dev -- commit hash: unset
; Z3 version (according to F*): 4.8.5

(push) ;; push{0
; <fuel='8' ifuel='2'>
;;; Fact-ids: 
(assert
 (! (= MaxFuel (SFuel (SFuel (SFuel (SFuel (SFuel (SFuel (SFuel (SFuel ZFuel)))))))))
  :named @MaxFuel_assumption))
;;; Fact-ids: 
(assert (! (= MaxIFuel (SFuel (SFuel ZFuel))) :named @MaxIFuel_assumption))
; query
;;; Fact-ids: 
(assert
 (! (not
   (forall ((@x0 Term))
    (! (implies
      (and
       (HasType @x0 (Prims.pure_post Tm_refine_7a42f32a02c9d8ce0b30070f062fc0f8))
       ;; def=Prims.fst(410,27-410,88); use=Clase01.fst(82,42-85,54)
       (forall ((@x1 Term))
        (! ;; def=Prims.fst(410,84-410,87); use=Clase01.fst(82,42-85,54)
         (Valid
          ;; def=Prims.fst(410,84-410,87); use=Clase01.fst(82,42-85,54)
          (ApplyTT @x0 @x1))
         :pattern ((ApplyTT @x0 @x1))
         :qid @query.1)))
      ;; def=Prims.fst(397,2-397,39); use=Clase01.fst(82,42-85,54)
      (and
       (implies
        ;; def=Clase01.fst(82,14-83,5); use=Clase01.fst(82,48-83,5)
        (= x_ae567c2fb75be05905677af440075565_0 (BoxInt 0))
        ;; def=Clase01.fst(82,31-82,37); use=Clase01.fst(83,9-83,10)
        (or
         label_1
         ;; def=Clase01.fst(82,31-82,37); use=Clase01.fst(83,9-83,10)
         (>= (BoxInt_proj_0 (BoxInt 1)) (BoxInt_proj_0 x_ae567c2fb75be05905677af440075565_0))))
       (implies
        ;; def=Prims.fst(397,19-397,21); use=Clase01.fst(82,42-85,54)
        (not
         ;; def=Clase01.fst(82,14-83,5); use=Clase01.fst(82,48-83,5)
         (= x_ae567c2fb75be05905677af440075565_0 (BoxInt 0)))
        ;; def=Prims.fst(397,2-397,39); use=Clase01.fst(82,42-85,54)
        (and
         (implies
          ;; def=Clase01.fst(82,14-84,5); use=Clase01.fst(82,48-84,5)
          (= x_ae567c2fb75be05905677af440075565_0 (BoxInt 1))
          ;; def=Clase01.fst(82,31-82,37); use=Clase01.fst(84,9-84,10)
          (or
           label_2
           ;; def=Clase01.fst(82,31-82,37); use=Clase01.fst(84,9-84,10)
           (>= (BoxInt_proj_0 (BoxInt 1)) (BoxInt_proj_0 x_ae567c2fb75be05905677af440075565_0))))
         (implies
          ;; def=Prims.fst(397,19-397,21); use=Clase01.fst(82,42-85,54)
          (not
           ;; def=Clase01.fst(82,14-84,5); use=Clase01.fst(82,48-84,5)
           (= x_ae567c2fb75be05905677af440075565_0 (BoxInt 1)))
          ;; def=Prims.fst(421,99-421,120); use=Clase01.fst(82,42-85,54)
          (forall ((@x1 Term))
           (! (implies
             (and
              (HasType @x1 Prims.int)
              ;; def=Clase01.fst(82,14-85,5); use=Clase01.fst(82,48-85,5)
              (= x_ae567c2fb75be05905677af440075565_0 @x1))
             (forall ((@x2 Term))
              (! (implies
                (and
                 (HasType @x2 (Prims.pure_post Tm_refine_7a42f32a02c9d8ce0b30070f062fc0f8))
                 ;; def=Prims.fst(410,27-410,88); use=Clase01.fst(82,42-85,54)
                 (forall ((@x3 Term))
                  (! ;; def=Prims.fst(410,84-410,87); use=Clase01.fst(82,42-85,54)
                   (Valid
                    ;; def=Prims.fst(410,84-410,87); use=Clase01.fst(82,42-85,54)
                    (ApplyTT @x2 @x3))
                   :pattern ((ApplyTT @x2 @x3))
                   :qid @query.4)))
                ;; def=Prims.fst(397,2-397,39); use=Clase01.fst(82,42-85,54)
                (and
                 (implies
                  ;; def=Clase01.fst(85,12-85,18); use=Clase01.fst(85,12-85,18)
                  (=
                   (Prims.op_GreaterThanOrEqual x_ae567c2fb75be05905677af440075565_0 (BoxInt 0))
                   (BoxBool true))
                  ;; def=Prims.fst(467,77-467,89); use=Clase01.fst(82,42-85,54)
                  (and
                   ;; def=Clase01.fst(82,42-85,54); use=Clase01.fst(85,29-85,34)
                   (or
                    label_3
                    ;; def=Clase01.fst(82,42-85,54); use=Clase01.fst(85,29-85,34)
                    (Valid
                     ;; def=Clase01.fst(82,42-85,54); use=Clase01.fst(85,29-85,34)
                     (Prims.precedes
                      Prims.int
                      Prims.int
                      (Prims.op_Subtraction x_ae567c2fb75be05905677af440075565_0 (BoxInt 1))
                      x_ae567c2fb75be05905677af440075565_0)))
                   ;; def=Prims.fst(364,2-364,58); use=Clase01.fst(82,42-85,54)
                   (forall ((@x3 Term))
                    (! (implies
                      (and
                       (HasType @x3 Tm_refine_c117e3dfa0913e9570f652c9d3f27f5b)
                       ;; def=Prims.fst(364,26-364,41); use=Clase01.fst(82,42-85,54)
                       (= @x3 (Prims.op_Subtraction x_ae567c2fb75be05905677af440075565_0 (BoxInt 1))))
                      ;; def=Prims.fst(459,66-459,102); use=Clase01.fst(82,42-85,54)
                      (forall ((@x4 Term))
                       (! (implies
                         (and
                          (HasType @x4 Tm_refine_14661f8e513c3c7ee26d003552553ce9)
                          ;; def=Clase01.fst(82,23-85,34); use=Clase01.fst(85,24-85,34)
                          (=
                           (Clase01.fib_
                            (Prims.op_Subtraction x_ae567c2fb75be05905677af440075565_0 (BoxInt 1)))
                           @x4))
                         ;; def=Prims.fst(364,2-364,58); use=Clase01.fst(82,42-85,54)
                         (forall ((@x5 Term))
                          (! (implies
                            (and
                             (HasType @x5 Tm_refine_14661f8e513c3c7ee26d003552553ce9)
                             ;; def=Prims.fst(364,26-364,41); use=Clase01.fst(82,42-85,54)
                             (=
                              @x5
                              (Clase01.fib_
                               (Prims.op_Subtraction x_ae567c2fb75be05905677af440075565_0 (BoxInt 1))))
                             ;; def=dummy(0,0-0,0); use=Clase01.fst(82,42-85,54)
                             (=
                              (Clase01.fib_
                               (Prims.op_Subtraction x_ae567c2fb75be05905677af440075565_0 (BoxInt 1)))
                              @x5))
                            ;; def=Prims.fst(467,77-467,89); use=Clase01.fst(82,42-85,54)
                            (and
                             ;; def=Clase01.fst(82,42-85,54); use=Clase01.fst(85,42-85,47)
                             (or
                              label_4
                              ;; def=Clase01.fst(82,42-85,54); use=Clase01.fst(85,42-85,47)
                              (Valid
                               ;; def=Clase01.fst(82,42-85,54); use=Clase01.fst(85,42-85,47)
                               (Prims.precedes
                                Prims.int
                                Prims.int
                                (Prims.op_Subtraction
                                 x_ae567c2fb75be05905677af440075565_0
                                 (BoxInt 2))
                                x_ae567c2fb75be05905677af440075565_0)))
                             ;; def=Prims.fst(364,2-364,58); use=Clase01.fst(82,42-85,54)
                             (forall ((@x6 Term))
                              (! (implies
                                (and
                                 (HasType @x6 Tm_refine_c117e3dfa0913e9570f652c9d3f27f5b)
                                 ;; def=Prims.fst(364,26-364,41); use=Clase01.fst(82,42-85,54)
                                 (=
                                  @x6
                                  (Prims.op_Subtraction
                                   x_ae567c2fb75be05905677af440075565_0
                                   (BoxInt 2))))
                                ;; def=Prims.fst(459,66-459,102); use=Clase01.fst(82,42-85,54)
                                (forall ((@x7 Term))
                                 (! (implies
                                   (and
                                    (HasType @x7 Tm_refine_4e6f2c3480a93437e1fa5631dd134168)
                                    ;; def=Clase01.fst(82,23-85,47); use=Clase01.fst(85,37-85,47)
                                    (=
                                     (Clase01.fib_
                                      (Prims.op_Subtraction
                                       x_ae567c2fb75be05905677af440075565_0
                                       (BoxInt 2)))
                                     @x7))
                                   ;; def=Prims.fst(364,2-364,58); use=Clase01.fst(82,42-85,54)
                                   (forall ((@x8 Term))
                                    (! (implies
                                      (and
                                       (HasType @x8 Tm_refine_4e6f2c3480a93437e1fa5631dd134168)
                                       ;; def=Prims.fst(364,26-364,41); use=Clase01.fst(82,42-85,54)
                                       (=
                                        @x8
                                        (Clase01.fib_
                                         (Prims.op_Subtraction
                                          x_ae567c2fb75be05905677af440075565_0
                                          (BoxInt 2))))
                                       ;; def=dummy(0,0-0,0); use=Clase01.fst(82,42-85,54)
                                       (=
                                        (Clase01.fib_
                                         (Prims.op_Subtraction
                                          x_ae567c2fb75be05905677af440075565_0
                                          (BoxInt 2)))
                                        @x8))
                                      ;; def=Prims.fst(459,66-459,102); use=Clase01.fst(82,42-85,54)
                                      (forall ((@x9 Term))
                                       (! (implies
                                         (and
                                          (HasType @x9 Prims.int)
                                          ;; def=Clase01.fst(82,23-85,47); use=Clase01.fst(82,42-85,54)
                                          (=
                                           (Prims.op_Addition
                                            (Clase01.fib_
                                             (Prims.op_Subtraction
                                              x_ae567c2fb75be05905677af440075565_0
                                              (BoxInt 1)))
                                            (Clase01.fib_
                                             (Prims.op_Subtraction
                                              x_ae567c2fb75be05905677af440075565_0
                                              (BoxInt 2))))
                                           @x9))
                                         ;; def=Clase01.fst(82,31-82,37); use=Clase01.fst(85,24-85,47)
                                         (or
                                          label_5
                                          ;; def=Clase01.fst(82,31-82,37); use=Clase01.fst(85,24-85,47)
                                          (>=
                                           (BoxInt_proj_0
                                            (Prims.op_Addition
                                             (Clase01.fib_
                                              (Prims.op_Subtraction
                                               x_ae567c2fb75be05905677af440075565_0
                                               (BoxInt 1)))
                                             (Clase01.fib_
                                              (Prims.op_Subtraction
                                               x_ae567c2fb75be05905677af440075565_0
                                               (BoxInt 2)))))
                                           (BoxInt_proj_0 x_ae567c2fb75be05905677af440075565_0))))
                                        :qid @query.11)))
                                     :qid @query.10)))
                                  :qid @query.9)))
                               :qid @query.8))))
                           :qid @query.7)))
                        :qid @query.6)))
                     :qid @query.5))))
                 (implies
                  ;; def=Prims.fst(397,19-397,21); use=Clase01.fst(82,42-85,54)
                  (not
                   ;; def=Clase01.fst(85,12-85,18); use=Clase01.fst(85,12-85,18)
                   (=
                    (Prims.op_GreaterThanOrEqual x_ae567c2fb75be05905677af440075565_0 (BoxInt 0))
                    (BoxBool true)))
                  ;; def=Prims.fst(421,99-421,120); use=Clase01.fst(82,42-85,54)
                  (forall ((@x3 Term))
                   (! (implies
                     (and
                      (HasType @x3 Prims.bool)
                      ;; def=Clase01.fst(85,12-85,54); use=Clase01.fst(85,12-85,54)
                      (=
                       (Prims.op_GreaterThanOrEqual x_ae567c2fb75be05905677af440075565_0 (BoxInt 0))
                       @x3))
                     ;; def=Clase01.fst(82,31-82,37); use=Clase01.fst(85,53-85,54)
                     (or
                      label_6
                      ;; def=Clase01.fst(82,31-82,37); use=Clase01.fst(85,53-85,54)
                      (>=
                       (BoxInt_proj_0 (BoxInt 1))
                       (BoxInt_proj_0 x_ae567c2fb75be05905677af440075565_0))))
                    :qid @query.12)))))
               :qid @query.3)))
            :qid @query.2)))))))
     :qid @query)))
  :named @query))
(set-option :rlimit 2723280)
(echo "<initial_stats>")
(echo "<statistics>") (get-info :all-statistics) (echo "</statistics>")
(echo "</initial_stats>")
(echo "<result>")
(check-sat)
(echo "</result>")
(set-option :rlimit 0)
(echo "<reason-unknown>") (get-info :reason-unknown) (echo "</reason-unknown>")
(echo "<labels>")
(echo "label_6")
(eval label_6)
(echo "label_5")
(eval label_5)
(echo "label_4")
(eval label_4)
(echo "label_3")
(eval label_3)
(echo "label_2")
(eval label_2)
(echo "label_1")
(eval label_1)
(echo "</labels>")
(echo "Done!")
(pop) ;; 0}pop

; QUERY ID: (Clase01.fib', 1)
; STATUS: unknown because (incomplete quantifiers)
