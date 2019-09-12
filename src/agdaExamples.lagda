%<*Nat>
\begin{code}
data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ
\end{code}
%</Nat>

%<*sum>
\begin{code}
_+_ : ℕ → ℕ → ℕ
zero + m = m
suc n + m = suc (n + m)
\end{code}
%</sum>

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
