import glob
import matplotlib.pyplot as plt

# Find all .sscr files recursively under ./isolated/
sscr_files = glob.glob('./isolated/**/*.sscr', recursive=True)

scores = []
for fname in sscr_files:
    with open(fname) as f:
        lines = [line.strip() for line in f if line.strip()]
        if len(lines) >= 6:
            try:
                score = int(lines[5])  # 6th line: total reached score
                scores.append(score)
            except ValueError:
                continue

plt.figure(figsize=(8,5))
plt.hist(scores, bins=range(min(scores), max(scores)+2), align='left', rwidth=0.8)
plt.xlabel('Total Reached Score')
plt.ylabel('Number of Snippets')
plt.title('Distribution of Snippet Scores')
plt.grid(axis='y')
plt.show()