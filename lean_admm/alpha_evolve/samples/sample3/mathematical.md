Let \( \mathbb{N} := \{0,1,2,\dots\} \).  
Let \( \varepsilon > 0, \, \mu > 1, \, c > 0, \, p > 1 \) be fixed real constants.  

Define sequences:  
\[
\{ r_k \}_{k \in \mathbb{N}}, \quad \{ s_k \}_{k \in \mathbb{N}}, \quad \{ \rho_k \}_{k \in \mathbb{N}} \subset \mathbb{R}_+.
\]  

Auxiliary definitions:  
\[
\tau_k := \frac{c}{(k+1)^p}, \qquad
\eta_k := \max(r_k, s_k, \varepsilon).
\]  

Normalized residuals:  
\[
\bar r_k := \frac{r_k}{\max(s_k, \varepsilon)}, \qquad
\bar s_k := \frac{s_k}{\max(r_k, \varepsilon)}.
\]  

Dynamic threshold:  
Define \( \ell_k := \log_{10}(\eta_k + 1) \).  
Define \( b_k \in \{2.0, 1.5, 1.2\} \) as follows:  
\[
b_k := 
\begin{cases}
2.0, & k < 5, \\
1.5, & 5 \le k < 15, \\
1.2, & k \ge 15.
\end{cases}
\]  
Define \( m_k \in \mathbb{R}_+ \):  
\[
m_k :=
\begin{cases}
1.5 + 0.1 \ell_k, & k < 5, \\
2.0 + 0.2 \ell_k, & 5 \le k < 15, \\
\mu + 0.3 \ell_k, & k \ge 15,
\end{cases}
\quad \text{then} \quad
\mu_k := \min(m_k, 10.0).
\]  

Excess ratio function: For \( x \ge \mu_k \),  
\[
E_k(x) := \min\left( \frac{x}{\mu_k}, 5.0 \right).
\]  

Scaling factor:  
\[
F_k(x) := 1 + (b_k - 1) \cdot \frac{\ln\big( E_k(x) \big)}{\ln(4)} - \tau_k, \qquad
\hat F_k(x) := \max\big( F_k(x), 1.05 \big).
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

Intermediate update:  
\[
\tilde \rho_{k+1} := 
\begin{cases}
\rho_k \cdot \hat F_k(\bar r_k), & \text{dir}_k = 1, \\
\rho_k / \hat F_k(\bar s_k), & \text{dir}_k = -1, \\
\rho_k, & \text{dir}_k = 0.
\end{cases}
\]  

Bounded change: Let \( M := 10.0 \).  
\[
\breve \rho_{k+1} :=
\begin{cases}
\rho_k \cdot M, & \tilde \rho_{k+1} > \rho_k \cdot M, \\
\rho_k / M, & \tilde \rho_{k+1} < \rho_k / M, \\
\tilde \rho_{k+1}, & \text{otherwise}.
\end{cases}
\]  

Final clipped value:  
\[
\rho_{k+1} := \min\big( \max( \breve \rho_{k+1}, 10^{-6} ), 10^{6} \big).
\]  

(Optional auxiliary for logging):  
\[
a_k := \max( \bar r_k, \bar s_k ).
\]