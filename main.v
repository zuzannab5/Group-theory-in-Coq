Require Import Setoid.


Record GroupTheo : Type := groupTheo
  { G : Set; (* nosnik *)
    op : G -> G -> G; (* operacja *)
    assoc : forall(x y z : G), op (op x y) z = op x (op y z);
    neut := forall(x : G), exists( e : G), op e x = x /\ op x e = x;
    inv := forall(x : G), exists( e y : G) , op x y = e /\ op y x  = e; 
  }.

