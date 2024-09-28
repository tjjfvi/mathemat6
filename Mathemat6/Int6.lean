import Mathemat6.Nat6

structure Diff where
  pos : Nat6
  neg : Nat6

def diff_eq (x y : Diff) : Prop :=
  x.pos + y.neg = y.pos + x.neg

instance : Setoid Diff where
  r := diff_eq
  iseqv := {
    refl := by intro x; rfl
    symm := by intro x y h; rw [diff_eq, h]
    trans := by
      intro x y z p q
      rw [diff_eq]
      rw [diff_eq] at p
      rw [diff_eq] at q
      rw [Nat6.add_comm] at p
      rw [Nat6.add_comm z.pos y.neg] at q
      rw [<- Nat6.add_cancel_left y.neg]
      rw [Nat6.add_assoc, Nat6.add_assoc]
      rw [p, <- q]
      rw [<- Nat6.add_assoc, <- Nat6.add_assoc]
      rw [Nat6.add_cancel_left, Nat6.add_comm]
  }

def Int6 := Quot diff_eq

def Int6.mk a b := Quot.mk diff_eq (Diff.mk a b)

def zero : Int6 := Int6.mk Nat6.zero Nat6.zero

instance (n : Nat) : OfNat Int6 n where
  ofNat := Int6.mk (Nat6.ofNat n) 0

variable (a b c : Int6)
variable (n m : Nat6)

theorem zero_eq_zero : Int6.mk n n = Int6.mk m m := by
  apply Quot.sound
  simp only [Setoid.r, diff_eq, Nat6.add_comm]

def add (a b : Int6) : Int6 := by
  apply Quotient.liftOn₂ a b (fun a b => Int6.mk (a.pos + b.pos) (a.neg + b.neg))
  intro a b x y p q
  apply Quot.sound
  simp only [Setoid.r, diff_eq]
  rw [Nat6.add_assoc, Nat6.add_assoc]
  rw [Nat6.add_comm_right b.pos x.neg]
  rw [p, <- Nat6.add_assoc, q, Nat6.add_assoc]
  rw [Nat6.add_comm_right a.neg y.pos]

instance : Add Int6 where
  add := add

def add_comm : a + b = b + a := by
  revert a b; apply Quotient.ind₂; intro a b
  simp only [Quotient.mk, Quot.mk, add, Quotient.liftOn₂, Quotient.lift₂, Quotient.lift, Int6.mk]
  apply Quot.sound
  simp only [Setoid.r, diff_eq]
  rw [Nat6.add_comm a.pos b.pos]
  rw [Nat6.add_comm b.neg a.neg]

def add_assoc : a + (b + c) = (a + b) + c := by
  revert a; apply Quotient.ind; intro a
  revert b; apply Quotient.ind; intro b
  revert c; apply Quotient.ind; intro c
  apply Quot.sound
  simp only [Setoid.r, diff_eq]
  repeat rw [Nat6.add_assoc]

def neg (a : Int6) : Int6 := by
  apply Quot.liftOn a (fun x => Int6.mk x.neg x.pos)
  intro a b h
  apply Quot.sound
  unfold diff_eq
  simp only
  rw [Nat6.add_comm, <- h, Nat6.add_comm]

instance : Neg Int6 where
  neg := neg

def neg_neg : -(-a) = a := by
  revert a; apply Quotient.ind; intro a
  apply Quot.sound
  simp only [diff_eq]

def add_inv_left : -a + a = zero := by
  revert a; apply Quotient.ind; intro a
  apply Quot.sound
  simp only [diff_eq]
  rw [Nat6.add_zero, Nat6.zero_add, Nat6.add_comm]

def add_inv_right : a + -a = zero := by
  rw [add_comm, add_inv_left]

def mul (a b : Int6) : Int6 := by
  apply Quotient.liftOn₂ a b
    (fun a b => Int6.mk
      (a.pos * b.pos + a.neg * b.neg)
      (a.pos * b.neg + a.neg * b.pos)
    )
  intro a b x y p q
  apply Quot.sound
  simp only [diff_eq]
  rw [<- Nat6.add_cancel_left (x.neg * b.pos)]
  repeat rw [Nat6.add_assoc]
  rw [<- Nat6.add_mul, Nat6.add_comm x.neg a.pos]
  rw [Nat6.add_comm (x.neg * b.pos)]
  rw [<- Nat6.add_assoc _ (x.neg * b.pos) _]
  rw [<- Nat6.mul_add]
  rw [<- Nat6.add_cancel_right (x.pos * b.pos)]
  rw [<- Nat6.add_assoc _ (a.neg * b.pos) (x.pos * b.pos)]
  rw [<- Nat6.add_mul]
  rw [Nat6.add_comm _ ((_ + _) * _), p, Nat6.add_comm x.pos a.neg]
  repeat rw [<- Nat6.add_assoc]
  rw [Nat6.add_cancel_left]
  repeat rw [Nat6.add_assoc]
  rw []
  rw [<- Nat6.add_cancel_right (x.neg * b.neg)]
  rw [Nat6.add_comm_right _ _ (_ * _ + _)]
  repeat rw [<- Nat6.add_assoc]
  rw [<- Nat6.add_mul]
  rw [<- Nat6.mul_add]
  rw [Nat6.add_comm (x.neg * (b.pos + y.neg))]
  repeat rw [Nat6.add_assoc]
  rw [q]
  rw [Nat6.add_cancel_right]
  rw [<- Nat6.add_cancel_left (x.pos * b.neg)]
  repeat rw [Nat6.add_assoc]
  rw [<- Nat6.add_mul, p]
  repeat rw [<- Nat6.add_assoc]
  rw [Nat6.add_comm]
  repeat rw [Nat6.add_assoc]
  rw [Nat6.add_cancel_right]
  repeat rw [<- Nat6.mul_add]
  rw [Nat6.add_comm, q, Nat6.add_comm]

instance : Mul Int6 where
  mul := mul

def mul_comm : a * b = b * a := by
  revert a b; apply Quotient.ind₂; intro a b
  apply Quot.sound
  simp only [diff_eq]
  repeat rw [Nat6.mul_comm b.pos, Nat6.mul_comm b.neg]
  rw [Nat6.add_comm (a.neg * b.pos)]

def mul_zero : a * zero = zero := by
  revert a; apply Quot.ind; intro a
  apply Quot.sound
  simp only [diff_eq, Nat6.mul_zero]
  rfl

def zero_mul : zero * a = zero := by
  revert a; apply Quot.ind; intro a
  apply Quot.sound
  simp only [diff_eq, Nat6.zero_mul]
  rfl

def mul_assoc : a * (b * c) = (a * b) * c := by
  revert a; apply Quotient.ind; intro a
  revert b; apply Quotient.ind; intro b
  revert c; apply Quotient.ind; intro c
  apply Quot.sound
  simp only [diff_eq]
  repeat rw [Nat6.mul_add]
  repeat rw [Nat6.add_mul]
  repeat rw [Nat6.mul_assoc]
  repeat rw [<- Nat6.add_assoc]
  rw [Nat6.add_cancel_left]
  apply Eq.symm
  rw [Nat6.add_comm_left]
  rw [Nat6.add_cancel_left]
  apply Eq.symm
  rw [Nat6.add_comm_left]
  rw [Nat6.add_cancel_left]
  rw [Nat6.add_cancel_left]
  rw [Nat6.add_cancel_left]
  rw [Nat6.add_comm_left]
  rw [Nat6.add_cancel_left]
  rw [Nat6.add_comm]

def mul_neg : a * -b = -(a * b) := by
  revert a; apply Quotient.ind; intro a
  revert b; apply Quotient.ind; intro b
  apply Quot.sound
  simp only [diff_eq]

def neg_mul : -a * b = -(a * b) := by
  rw [mul_comm, mul_neg, mul_comm]
