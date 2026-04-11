import numpy as np


def perceptron(X, y):
    """Run the Perceptron algorithm (Rosenblatt 1958) on a sequence.

    Args:
        X: array of shape (T, d), inputs.
        y: array of shape (T,), labels in {-1, +1}.

    Returns:
        mistakes: total number of mistakes.
        w: final weight vector.
    """
    X = np.asarray(X, dtype=float)
    T, d = X.shape
    w = np.zeros(d)
    mistakes = 0

    for t in range(T):
        y_hat = 1 if w @ X[t] >= 0 else -1
        if y_hat != y[t]:
            mistakes += 1
            w = w + y[t] * X[t]

    return mistakes, w


def generate_separable_data(T, d, gamma, u, R=1.0, rng=None):
    """Generate linearly separable data with known margin gamma and norm bound R.

    Points are sampled uniformly in the ball of radius R and rejected if
    |<u, x>| < gamma. Label is sign(<u, x>).

    Args:
        T: number of examples.
        d: dimension.
        gamma: margin (must satisfy 0 < gamma <= R).
        u: unit separator vector of shape (d,).
        R: norm bound on examples.
        rng: numpy Generator instance.

    Returns:
        X: array of shape (T, d).
        y: array of shape (T,), labels in {-1, +1}.
    """
    if rng is None:
        rng = np.random.default_rng(0)

    assert 0 < gamma <= R

    u = np.asarray(u, dtype=float)
    X = np.empty((T, d))
    y = np.empty(T, dtype=int)
    n = 0

    while n < T:
        z = rng.standard_normal(d)
        z *= R * rng.uniform() ** (1 / d) / np.linalg.norm(z)
        proj = u @ z
        if abs(proj) < gamma:
            continue
        X[n] = z
        y[n] = 1 if proj >= 0 else -1
        n += 1

    return X, y
