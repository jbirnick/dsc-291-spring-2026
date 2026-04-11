import numpy as np
import matplotlib.pyplot as plt
from perceptron import perceptron, generate_separable_data

d = 10
T = 10000
R = 1.0
gammas = np.logspace(np.log10(0.02), np.log10(0.5), 15)
n_trials = 30

u = np.zeros(d)
u[0] = 1.0

avg_mistakes = np.empty(len(gammas))

for i, gamma in enumerate(gammas):
    rng = np.random.default_rng(0)
    total = 0
    for _ in range(n_trials):
        X, y = generate_separable_data(T, d, gamma, u, R=R, rng=rng)
        m, _ = perceptron(X, y)
        total += m
    avg_mistakes[i] = total / n_trials

inv_gamma_sq = 1 / gammas**2

fig, ax = plt.subplots(figsize=(6, 4))
ax.scatter(inv_gamma_sq, avg_mistakes, s=20, zorder=3, label="Perceptron (avg)")
ax.plot(inv_gamma_sq, R**2 * inv_gamma_sq, "k--", label=r"$R^2/\gamma^2$ bound")
ax.set_xlabel(r"$1/\gamma^2$")
ax.set_ylabel("Mistakes")
ax.set_xscale("log")
ax.set_yscale("log")
ax.legend()
ax.set_title(r"Perceptron mistakes as $\gamma \to 0$")
fig.tight_layout()
fig.savefig("plot_gamma_zero.png", dpi=150)
