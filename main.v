Require Import Setoid.


Record GroupTheo : Type := groupTheo
  { G : Set; (* nosnik *)
    op : G -> G -> G; (* operacja *)
    assoc : forall(x y z : G), op (op x y) z = op x (op y z);
    neut := forall(x : G), exists( e : G), op e x = x /\ op x e = x;
    inv := forall(x : G), exists( e y : G) , op x y = e /\ op y x  = e; 
  }.

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
