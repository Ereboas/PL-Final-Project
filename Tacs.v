Ltac expand x := unfold x; fold x.
Ltac inv H := inversion H; subst.
Ltac invc H := inv H; clear H.
