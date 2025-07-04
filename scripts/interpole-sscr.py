import glob
import matplotlib.pyplot as plt
import numpy as np
from scipy.optimize import curve_fit, minimize
from functools import partial

# Find all .sscr files recursively under ./isolated/
sscr_files = glob.glob('./isolated/**/*.sscr', recursive=True)

norm_scores = []
for fname in sscr_files:
    with open(fname) as f:
        lines = [line.strip() for line in f if line.strip()]
        if len(lines) >= 6:
            try:
                max_score = int(lines[4])  # 5th line: max possible score
                reached_score = int(lines[5])  # 6th line: total reached score
                if max_score > 0:
                    norm_scores.append(reached_score / max_score)
            except ValueError:
                continue

# Histogram (get counts, not density)
counts, bins = np.histogram(norm_scores, bins=20, range=(0,1))
counts = counts / counts.sum()  # Normalize so sum(counts) == 1

# Bin centers for fitting
bin_centers = 0.5 * (bins[1:] + bins[:-1])
mask = counts > 0
weights = (counts[mask])**2

# General constrained polynomial fit for degree n (force p(0.2)=0, p(1)=1)
def constrained_poly_loss_n(coeffs, x, y, weights, n):
    # coeffs: [a, b, ..., z] (no constant term)
    # p(x) = a*x^n + b*x^{n-1} + ... + y*x
    # Constraints: p(0.2) = 0, p(1) = 1
    p_x = sum(c * x**(n-i) for i, c in enumerate(coeffs))
    loss = np.sum(weights * (p_x - y)**4)
    # Penalty for constraint violation at x=1 and x=0.2
    penalty = 1e6 * (sum(coeffs) - 1)**2
    penalty += 1e6 * (sum(c * 0.2**(n-i) for i, c in enumerate(coeffs)))**2
    return loss + penalty

x_fit = np.linspace(0, 1, 200)
plt.figure(figsize=(8,5))
plt.bar(0.5 * (bins[1:] + bins[:-1]), counts, width=(bins[1]-bins[0]), alpha=0.6, label='Normalized Score Histogram')
plt.xlim(0, 1)
plt.ylim(0, 1)

colors = ['b', 'c', 'm', 'g', 'r']
for deg in range(1, 6):
    # Initial guess: fit unconstrained, then remove constant term
    init = np.polyfit(bin_centers[mask], counts[mask], deg, w=weights)
    init = init[:-1]
    # Minimize with constraint
    res = minimize(partial(constrained_poly_loss_n, x=bin_centers[mask], y=counts[mask], weights=weights, n=deg), init, method='BFGS')
    coeffs = list(res.x)
    # Adjust last coeff so sum(coeffs) == 1
    sum_except_last = sum(coeffs)
    last = 1 - sum_except_last
    coeffs.append(last)
    # Compose polynomial (no constant term)
    poly_coeffs = np.array(coeffs)
    poly = np.poly1d(poly_coeffs)
    y_fit = poly(x_fit)
    plt.plot(x_fit, y_fit, color=colors[deg-1], label=f'Degree {deg} constrained')

plt.xlabel('Normalized Score')
plt.ylabel('Fraction of Snippets')
plt.title('Distribution of Normalized Snippet Scores')
plt.legend()
plt.grid(axis='y')
plt.show()