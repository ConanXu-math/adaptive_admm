Let \( \mathbb{N} := \{0,1,2,\dots\} \).  
Let \( \varepsilon > 0, \, \mu > 1, \, c > 0, \, p > 1 \) be fixed real constants.  

Define sequences:  
\[
\{ r_k \}_{k \in \mathbb{N}}, \quad \{ s_k \}_{k \in \mathbb{N}}, \quad \{ \rho_k \}_{k \in \mathbb{N}} \subset \mathbb{R}_+.
\]  

Auxiliary definition:  
\[
\tau_k := \frac{c}{(k+1)^p}, \qquad k \in \mathbb{N}.
\]  

Normalized residuals:  
\[
\bar r_k := \frac{r_k}{\max(s_k, \varepsilon)}, \qquad
\bar s_k := \frac{s_k}{\max(r_k, \varepsilon)}.
\]  

Dynamic threshold:  
\[
\mu_k := 
\begin{cases}
2.0, & k < 10, \\
\mu, & k \ge 10.
\end{cases}
\]  

Base factor (iteration‑dependent):  
\[
\beta_k := 
\begin{cases}
1.5, & k < 5, \\
1.2, & 5 \le k < 20, \\
1.1, & k \ge 20.
\end{cases}
\]  

Update factor:  
\[
\gamma_k := \max\big( \beta_k - \tau_k, 1.05 \big).
\]  

Direction function \( \text{dir}_k \in \{1, -1, 0\} \):  
\[
\text{dir}_k := 
\begin{cases}
1, & \bar r_k > \mu_k, \\
-1, & \bar s_k > \mu_k, \\
0, & \text{otherwise}.
\end{cases}
\]  

Recurrence for \( \rho_k \):  
\[
\rho_{k+1} := 
\begin{cases}
\rho_k \cdot \gamma_k, & \text{dir}_k = 1, \\
\rho_k / \gamma_k, & \text{dir}_k = -1, \\
\rho_k, & \text{dir}_k = 0,
\end{cases}
\qquad k \in \mathbb{N}.
\]  

Post‑update clipping:  
\[
\rho_{k+1} := \min\big( \max( \rho_{k+1}, 10^{-6} ), 10^{6} \big).
\]  

(Optional auxiliary for logging):  
\[
a_k := \max( \bar r_k, \bar s_k ).
\]