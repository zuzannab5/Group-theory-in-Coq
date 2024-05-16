Require Import Setoid.


Record GroupTheo : Type := groupTheo
  { G : Set; (* nosnik *)
    op : G -> G -> G; (* operacja *)
    assoc : forall(x y z : G), op (op x y) z = op x (op y z);
    neut := forall(x : G), exists( e : G), op e x = x /\ op x e = x;
    inv := forall(x : G), exists( e y : G) , op x y = e /\ op y x  = e; 
  }.

(* Jednoznaczność elementu neutralnego *)
Definition idPro (g : GroupTheo ) (e : G g) := (forall(x : G g), op g e x = x /\ op g x e = x).

Theorem exOnlyOne : forall (g : GroupTheo), forall( e f : G g), (idPro g e /\ idPro g f) -> e = f.
Proof.  
  unfold idPro.
  intros.
  destruct H.
  pose proof H f as F.
  pose proof H0 e as E.
  destruct E.
  destruct F.
  rewrite <- H2.
  trivial.
Qed.

(* Jednoznaczność elementu odwrotnego *)
Definition invPro (g : GroupTheo) (e y : G g):= idPro g e /\ ( forall(x : G g) ,( op g x y = e /\ op g y x  = e)).

Theorem exOnlyOneInv : forall( g : GroupTheo), forall (e y1 y2 x : G g), invPro g e y1 /\ invPro g e y2 -> y1 = y2.
Proof.
  unfold invPro.
  unfold idPro.
  intros.
  destruct H.
  destruct H.
  destruct H0.
  pose proof H y1.
  destruct H3.
  pose proof H y2.
  destruct H5.
  rewrite <- H4.
  rewrite <- H5.
  pose proof H1 x.
  pose proof H2 x.
  destruct H7.
  destruct H8.
  rewrite <- H8 at 1.
  rewrite <- H9 at 1.
  rewrite (assoc ).
  trivial.
Qed.


Record Group : Type := group
  { G : Set; (* nosnik *)
    op : G -> G -> G; (* operacja *)
    inv : G -> G;
    e : G;
  
    assoc : forall(x y z : G), op (op x y) z = op x (op y z);
    id :  forall(x : G), op e x = e /\ op x e = e ;
    inverse :  forall(x : G), op x (inv x) = e /\ op (inv x) x  = e ;
  }.