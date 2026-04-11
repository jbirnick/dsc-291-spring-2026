import numpy as np
import matplotlib.pyplot as plt
from perceptron import perceptron, generate_separable_data

dims = [2, 5, 10, 20, 50]
gamma = 0.1
R = 1.0
T = 2000
n_trials = 30

avg_mistakes = []

for d in dims:
    u = np.zeros(d)
    u[0] = 1.0
    rng = np.random.default_rng(0)
    total = 0
    for _ in range(n_trials):
        X, y = generate_separable_data(T, d, gamma, u, R=R, rng=rng)
        m, _ = perceptron(X, y)
        total += m
    avg_mistakes.append(total / n_trials)

bound = R**2 / gamma**2

fig, ax = plt.subplots(figsize=(6, 4))
ax.plot(dims, avg_mistakes, "o-", label="Perceptron (avg)")
ax.axhline(bound, color="k", linestyle="--", label=rf"$R^2/\gamma^2 = {bound:.0f}$")
ax.set_xlabel("Dimension $d$")
ax.set_ylabel("Mistakes")
ax.set_xscale("log")
ax.legend()
ax.set_title(r"Perceptron mistakes vs dimension ($\gamma=0.1$, $R=1$)")
fig.tight_layout()
fig.savefig("plot_dimension.png", dpi=150)
