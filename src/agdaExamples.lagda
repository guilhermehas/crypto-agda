%<*Nat>
\begin{code}
data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ
\end{code}
%</Nat>

%<*NatElim>
\begin{code}
ℕ-elim : (target : ℕ) (motive : (ℕ → Set)) (base : motive zero)
  (step : (n : ℕ) → motive n → motive (suc n) ) → motive target
ℕ-elim zero motive base step = base
ℕ-elim (suc target) motive base step = step target (ℕ-elim target motive base step)
\end{code}
%</NatElim>

%<*sumElim>
\begin{code}
_+_ : ℕ → ℕ → ℕ
n + m = ℕ-elim n (λ _ → ℕ) m λ _ v → suc v
\end{code}
%</sumElim>

%<*sum>
\begin{code}
_+'_ : ℕ → ℕ → ℕ
zero +' m = m
suc n +' m = suc (n + m)
\end{code}
%</sum>

<%trivialType>
\begin{code}
data ⊤ : Set where
  tt : ⊤
\end{code}
%</trivialType>

<%botType>
\begin{code}
data ⊥ : Set where

⊥-elim : {A : Set} (bot : ⊥) → A
⊥-elim ()
\end{code}
%</botType>

<%eitherType>
\begin{code}
data Either (A : Set) (B : Set) : Set where
  left  : (l : A) → Either A B
  right : (r : B) → Either A B

Either-elim : {A B : Set} {motive : (eab : Either A B) → Set}
  (target : Either A B)
  (on-left  : (l : A) → (motive (left  l)))
  (on-right : (r : B) → (motive (right r)))
  ------------------------------------------
  → motive target
Either-elim (left  l) onleft onright = onleft  l
Either-elim (right r) onleft onright = onright r
\end{code}
%</eitherType>

<%boolType>
\begin{code}
Bool : Set
Bool = Either ⊤ ⊤
\end{code}
%</boolType>

<%ifThenElse>
\begin{code}
if_then_else_ : {A : Set} (b : Bool) (tRes fRes : A) → A
if b then tRes else fRes = Either-elim b (λ _ → tRes) λ _ → fRes
\end{code}
%</ifThenElse>

<%piType>
\begin{code}
∀-elim : ∀ {A : Set} {B : A → Set}
  → (L : ∀ (x : A) → B x)
  → (M : A)
  -----------------
  → B M
∀-elim L M = L M
\end{code}
%</piType>

%<*sumType>
\begin{code}
data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B

Σ-elim : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C)
  → Σ A B
  ---------------
  → C
Σ-elim f ⟨ x , y ⟩ = f x y
\end{code}
%</sumType>

\begin{code}
infixr 5 _::_

data Vector {a} (A : Set a) : ℕ → Set a where
  []  : Vector A zero
  _::_ : ∀ {n} (x : A) (xs : Vector A n) → Vector A (suc n)

Matrix : (A : Set) (m : ℕ) (n : ℕ) → Set
Matrix A m n = Vector (Vector A n) m
\end{code}

%<*vecHead>
\begin{code}
head : {A : Set} {n : ℕ} (vec : Vector A (suc n)) → A
head (x :: vec) = x
\end{code}
%</vecHead>

\begin{code}
_+v_ : {n : ℕ} (P Q : Vector ℕ n) → Vector ℕ n
[] +v [] = []
(x :: P) +v (y :: Q) = (x + y) :: (P +v Q)
\end{code}

%<*matrixSum>
\begin{code}
_+m_ : {m n : ℕ} (P Q : Matrix ℕ m n) → Matrix ℕ m n
[] +m [] = []
(vx :: P) +m (vy :: Q) = (vx +v vy) :: (P +m Q)
\end{code}
%</matrixSum>
