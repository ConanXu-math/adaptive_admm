Let \( \mathbb{N} := \{0,1,2,\dots\} \).  
Let \( \varepsilon > 0 \) and \( \mu > 1 \) be fixed real constants.  
Let \( c > 0, p > 1 \) be fixed real constants.  

Define sequences:  
\[
\{ r_k \}_{k \in \mathbb{N}}, \quad \{ s_k \}_{k \in \mathbb{N}}, \quad \{ \rho_k \}_{k \in \mathbb{N}} \subset \mathbb{R}_+, \quad \{ \tau_k \}_{k \in \mathbb{N}} \subset \mathbb{R}_+.
\]  

Auxiliary definition:  
\[
\tau_k := \frac{c}{(k+1)^p}, \qquad k \in \mathbb{N}.
\]  

Define for each \( k \):  
\[
\bar r_k := \frac{r_k}{\max(s_k, \varepsilon)}, \qquad
\bar s_k := \frac{s_k}{\max(r_k, \varepsilon)}.
\]  

Define direction function \( \text{dir}_k \in \{-1,0,1\} \):  
\[
\text{dir}_k := 
\begin{cases}
1, & \bar r_k > \mu, \\
-1, & \bar s_k > \mu, \\
0, & \text{otherwise}.
\end{cases}
\]  

Recurrence for \( \rho_k \):  
\[
\rho_{k+1} := 
\begin{cases}
\rho_k (1 + \tau_k), & \text{dir}_k = 1, \\
\rho_k / (1 + \tau_k), & \text{dir}_k = -1, \\
\rho_k, & \text{dir}_k = 0,
\end{cases}
\qquad k \in \mathbb{N}.
\]  

Post-update clipping:  
\[
\rho_{k+1} := \min\big( \max( \rho_{k+1}, 10^{-6} ), 10^{6} \big).
\]  

(Optional auxiliary for logging):  
\[
a_k := \max( \bar r_k, \bar s_k ).
\]