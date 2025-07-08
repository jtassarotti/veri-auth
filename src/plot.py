import matplotlib.pyplot as plt
import statistics
import os
import csv

def get_times_lauth(s):
  sl = [i.split("+-") for i in s.split() if ("+-" in i)]
  return [1./float(i[0]) if "/s" in i[1] else float(i[0]) for i in sl]

results_folder = "results/"

auth_data_rb_ins = open("results/auth_rb_401.txt").read()
lauthp_data_rb_ins = open("results/lauth_rb_prv.txt").read()
lauthv_data_rb_ins = open("results/lauth_rb_vrf.txt").read()

data_mtree_look = open("results/auth_mtree_401.txt").read()

auth_data_rb_look = open("results/auth_rb_look_401.txt").read()
lauthp_data_rb_look = open("results/lauth_rb_look_prv.txt").read()
lauthv_data_rb_look = open("results/lauth_rb_look_vrf.txt").read()

data_mtree_upd = open("results/auth_mtree_upd_401.txt").read()

d = {}
auth_times_rb_ins = [line for line in auth_data_rb_ins.split("Profiling:\n")[1].split("\n")[:-1]]
auth_times_mtree_look = [line for line in data_mtree_look.split("Profiling:\n")[1].split("\n")[:-1]]
auth_times_rb_look = [line for line in auth_data_rb_look.split("Profiling:\n")[1].split("\n")[:-1]]
auth_times_mtree_upd = [line for line in data_mtree_upd.split("Profiling:\n")[1].split("\n")[:-1]]
for i in (auth_times_rb_ins+auth_times_mtree_look+auth_times_rb_look+auth_times_mtree_upd):
  s = i.split()
  if s[0] not in d:
    d[s[0]] = {}
  rest = " ".join(s[1:])
  size = int(rest.split(".")[0])
  times = [float(i) for i in sorted(s[-1].split("_")[:-1])]
  d[s[0]][size] = statistics.median(times)

dirprover_redblack_io_insertions = [d["dirprover_redblack_io_insertions"][i] for i in range(4, 22)]
dirprover_redblack_poly_io_insertions = [d["dirprover_redblack_poly_io_insertions"][i] for i in range(4, 22)]
dirprover_redblack_poly_mar_ser_io_insertions = [d["dirprover_redblack_poly_mar_ser_io_insertions"][i] for i in range(4, 22)]
prover_io_redblack_insertions = [d["prover_io_redblack_insertions"][i] for i in range(4, 22)]
dirverifier_redblack_io_insertions = [d["dirverifier_redblack_io_insertions"][i] for i in range(4, 22)]
dirverifier_redblack_poly_io_insertions = [d["dirverifier_redblack_poly_io_insertions"][i] for i in range(4, 22)]
dirverifier_redblack_poly_mar_ser_io_insertions = [d["dirverifier_redblack_poly_mar_ser_io_insertions"][i] for i in range(4, 22)]
verifier_io_redblack_insertions = [d["verifier_io_redblack_insertions"][i] for i in range(4, 22)]
lauth_prover_rb_insertions = get_times_lauth(lauthp_data_rb_ins)
lauth_verifier_rb_insertions = get_times_lauth(lauthv_data_rb_ins)

dirprover_merkle_io_retrieves = [d["dirprover_merkle_io_retrieves"][i] for i in range(4, 20)]
dirprover_merkle_poly_io_retrieves = [d["dirprover_merkle_poly_io_retrieves"][i] for i in range(4, 20)]
dirprover_merkle_poly_mar_ser_io_retrieves = [d["dirprover_merkle_poly_mar_ser_io_retrieves"][i] for i in range(4, 20)]
prover_io_merkle_retrieves = [d["prover_io_merkle_retrieves"][i] for i in range(4, 20)]
dirverifier_merkle_io_retrieves = [d["dirverifier_merkle_io_retrieves"][i] for i in range(4, 20)]
dirverifier_merkle_poly_io_retrieves = [d["dirverifier_merkle_poly_io_retrieves"][i] for i in range(4, 20)]
dirverifier_merkle_poly_mar_ser_io_retrieves = [d["dirverifier_merkle_poly_mar_ser_io_retrieves"][i] for i in range(4, 20)]
verifier_io_merkle_retrieves = [d["verifier_io_merkle_retrieves"][i] for i in range(4, 20)]
lauth_prover_merkle_retrieves = [d["lambda_auth_merkle_prover_retrieves"][i] for i in range(4, 20)]
lauth_verifier_merkle_retrieves = [d["lambda_auth_merkle_verifier_retrieves"][i] for i in range(4, 20)]

dirprover_redblack_io_retrieves = [d["dirprover_redblack_io_retrieves"][i] for i in range(4, 22)]
dirprover_redblack_poly_io_retrieves = [d["dirprover_redblack_poly_io_retrieves"][i] for i in range(4, 22)]
dirprover_redblack_poly_mar_ser_io_retrieves = [d["dirprover_redblack_poly_mar_ser_io_retrieves"][i] for i in range(4, 22)]
prover_io_redblack_retrieves = [d["prover_io_redblack_retrieves"][i] for i in range(4, 22)]
dirverifier_redblack_io_retrieves = [d["dirverifier_redblack_io_retrieves"][i] for i in range(4, 22)]
dirverifier_redblack_poly_io_retrieves = [d["dirverifier_redblack_poly_io_retrieves"][i] for i in range(4, 22)]
dirverifier_redblack_poly_mar_ser_io_retrieves = [d["dirverifier_redblack_poly_mar_ser_io_retrieves"][i] for i in range(4, 22)]
verifier_io_redblack_retrieves = [d["verifier_io_redblack_retrieves"][i] for i in range(4, 22)]
lauth_prover_rb_retrieves = get_times_lauth(lauthp_data_rb_look)
lauth_verifier_rb_retrieves = get_times_lauth(lauthv_data_rb_look)

dirprover_merkle_io_updates = [d["dirprover_merkle_io_updates"][i] for i in range(4, 20)]
dirprover_merkle_poly_io_updates = [d["dirprover_merkle_poly_io_updates"][i] for i in range(4, 20)]
dirprover_merkle_poly_mar_ser_io_updates = [d["dirprover_merkle_poly_mar_ser_io_updates"][i] for i in range(4, 20)]
prover_io_merkle_updates = [d["prover_io_merkle_updates"][i] for i in range(4, 20)]
dirverifier_merkle_io_updates = [d["dirverifier_merkle_io_updates"][i] for i in range(4, 20)]
dirverifier_merkle_poly_io_updates = [d["dirverifier_merkle_poly_io_updates"][i] for i in range(4, 20)]
dirverifier_merkle_poly_mar_ser_io_updates = [d["dirverifier_merkle_poly_mar_ser_io_updates"][i] for i in range(4, 20)]
verifier_io_merkle_updates = [d["verifier_io_merkle_updates"][i] for i in range(4, 20)]
lauth_prover_merkle_updates = [d["lambda_auth_merkle_prover_updates"][i] for i in range(4, 20)]
lauth_verifier_merkle_updates = [d["lambda_auth_merkle_verifier_updates"][i] for i in range(4, 20)]


x_rb = [i for i in range(4, 22)]
x_mtree = [i for i in range(4, 20)]
plt.rcParams.update({'axes.labelsize': 8, 'legend.fontsize': 7, 'xtick.labelsize': 6, 'ytick.labelsize': 6})
# plt.rcParams['text.usetex'] = True
plt.rcParams['svg.fonttype'] = 'none'
fig, axs = plt.subplots(2, 2, figsize=(8, 8))
axs[0, 0].plot(x_rb, prover_io_redblack_insertions, label='authentikit', marker = '.')
axs[0, 0].plot(x_rb, dirprover_redblack_poly_mar_ser_io_insertions, label='authentikit-functor', linestyle='dotted')
axs[0, 0].plot(x_rb, dirprover_redblack_poly_io_insertions, label='authentikit-functor-prepare', linestyle='dashed')
axs[0, 0].plot(x_rb, dirprover_redblack_io_insertions, label='authentikit-functor-prepare-poly', marker = ',')
axs[0, 0].plot(x_rb, lauth_prover_rb_insertions, label=r"$\lambda\bullet$", marker = '|')
axs[0, 0].set_title("Prover ablation")
axs[0, 0].set_ylabel("Running time for 100,000\nredblack insertions (s)")
axs[0, 0].tick_params(labelsize='6')

axs[0, 1].plot(x_rb, verifier_io_redblack_insertions, label='authentikit', marker = '.')
axs[0, 1].plot(x_rb, dirverifier_redblack_poly_mar_ser_io_insertions, label='authentikit-functor', linestyle='dotted')
axs[0, 1].plot(x_rb, dirverifier_redblack_poly_io_insertions, label='authentikit-functor-prepare', linestyle='dashed')
axs[0, 1].plot(x_rb, dirverifier_redblack_io_insertions, label='authentikit-functor-prepare-poly', marker = ',')
axs[0, 1].plot(x_rb, lauth_verifier_rb_insertions, label=r"$\lambda\bullet$", marker = '|')
axs[0, 1].set_title("Verifier ablation")
axs[0, 1].tick_params(labelsize='6')

axs[1, 0].plot(x_mtree, prover_io_merkle_retrieves, label='authentikit', marker = '.')
axs[1, 0].plot(x_mtree, dirprover_merkle_poly_mar_ser_io_retrieves, label='authentikit-functor', linestyle='dotted')
axs[1, 0].plot(x_mtree, dirprover_merkle_poly_io_retrieves, label='authentikit-functor-prepare', linestyle='dashed')
axs[1, 0].plot(x_mtree, dirprover_merkle_io_retrieves, label='authentikit-functor-prepare-poly', marker = ',')
axs[1, 0].plot(x_mtree, lauth_prover_merkle_retrieves, label=r"$\lambda\bullet$", marker = '|')
axs[1, 0].set_xlabel("Tree size (log)")
axs[1, 0].set_ylabel("Running time for 100,000\nmerkle retrieves (s)")
axs[1, 0].tick_params(labelsize='6')

axs[1, 1].plot(x_mtree, verifier_io_merkle_retrieves, label='authentikit', marker = '.')
axs[1, 1].plot(x_mtree, dirverifier_merkle_poly_mar_ser_io_retrieves, label='authentikit-functor', linestyle='dotted')
axs[1, 1].plot(x_mtree, dirverifier_merkle_poly_io_retrieves, label='authentikit-functor-prepare', linestyle='dashed')
axs[1, 1].plot(x_mtree, dirverifier_merkle_io_retrieves, label='authentikit-functor-prepare-poly', marker = ',')
axs[1, 1].plot(x_mtree, lauth_verifier_merkle_retrieves, label=r"$\lambda\bullet$", marker = '|')
axs[1, 1].set_xlabel("Tree size (log)")
axs[1, 1].tick_params(labelsize='6')

plt.legend(loc='upper center', bbox_to_anchor=(-0.23, -0.2), ncols=2, frameon=False)
plt.savefig("results/ablation.png", bbox_inches='tight')


# fig, axs = plt.subplots(1, 2, figsize=(12, 3))
# axs[0].plot(x_rb, prover_io_redblack_retrieves, label='authentikit')
# axs[0].plot(x_rb, dirprover_redblack_poly_mar_ser_io_retrieves, label='authentikit-functor')
# axs[0].plot(x_rb, dirprover_redblack_poly_io_retrieves, label='authentikit-functor-prepare')
# axs[0].plot(x_rb, dirprover_redblack_io_retrieves, label='authentikit-functor-prepare-poly')
# axs[0].plot(x_rb, lauth_prover_rb_retrieves, label=r"$\lambda\bullet$")
# axs[0].set_title("Prover ablation")
# axs[0].set_ylabel("Running time for 100,000\nredblack retrieves (s)")
# axs[0].tick_params(labelsize='6')

# axs[1].plot(x_rb, verifier_io_redblack_retrieves, label='authentikit')
# axs[1].plot(x_rb, dirverifier_redblack_poly_mar_ser_io_retrieves, label='authentikit-functor')
# axs[1].plot(x_rb, dirverifier_redblack_poly_io_retrieves, label='authentikit-functor-prepare')
# axs[1].plot(x_rb, dirverifier_redblack_io_retrieves, label='authentikit-functor-prepare-poly')
# axs[1].plot(x_rb, lauth_verifier_rb_retrieves, label=r"$\lambda\bullet$")
# axs[1].set_title("Verifier ablation")
# axs[1].tick_params(labelsize='6')

# plt.legend(loc='upper center', bbox_to_anchor=(-0.12, -0.2), ncols=2)
# plt.savefig("results/rb_look_ablation.png", bbox_inches='tight')


# fig, axs = plt.subplots(1, 2, figsize=(12, 3))
# axs[0].plot(x_mtree, prover_io_merkle_updates, label='authentikit')
# axs[0].plot(x_mtree, dirprover_merkle_poly_mar_ser_io_updates, label='authentikit-functor')
# axs[0].plot(x_mtree, dirprover_merkle_poly_io_updates, label='authentikit-functor-prepare')
# axs[0].plot(x_mtree, dirprover_merkle_io_updates, label='authentikit-functor-prepare-poly')
# axs[0].plot(x_mtree, lauth_prover_merkle_updates, label=r"$\lambda\bullet$")
# axs[0].set_xlabel("Tree size (log)")
# axs[0].set_ylabel("Running time for 100,000\nmerkle updates (s)")
# axs[0].tick_params(labelsize='6')

# axs[1].plot(x_mtree, verifier_io_merkle_updates, label='authentikit')
# axs[1].plot(x_mtree, dirverifier_merkle_poly_mar_ser_io_updates, label='authentikit-functor')
# axs[1].plot(x_mtree, dirverifier_merkle_poly_io_updates, label='authentikit-functor-prepare')
# axs[1].plot(x_mtree, dirverifier_merkle_io_updates, label='authentikit-functor-prepare-poly')
# axs[1].plot(x_mtree, lauth_verifier_merkle_updates, label=r"$\lambda\bullet$")
# axs[1].set_xlabel("Tree size (log)")
# axs[1].tick_params(labelsize='6')

# plt.legend(loc='upper center', bbox_to_anchor=(-0.12, -0.2), ncols=2)
# plt.savefig("results/mtree_upd_ablation.png", bbox_inches='tight')

# Helper to format float values to 5 digits
def fmt(val):
  if isinstance(val, float):
    return f"{val:.5f}"
  return val

# Write CSV files for redblack and merkle arrays with 5-digit float formatting (row-wise: size, col-wise: arrays)
def write_csv(path, arrays, indices, header=None):
  with open(path, "w", newline="") as csvfile:
    writer = csv.writer(csvfile)
    if header:
      writer.writerow(header)
    else:
      writer.writerow(["tree_size"] + [name for name, _ in arrays])
    for i in indices:
      row = [str(i + 4)]
      for _, arr in arrays:
        v = arr[i] if i < len(arr) else ""
        row.append(fmt(v) if v != "" else "")
      writer.writerow(row)

# Redblack arrays (insertions and retrieves)
rb_arrays = [
  ("dirprover_redblack_io_insertions", dirprover_redblack_io_insertions),
  ("dirprover_redblack_poly_io_insertions", dirprover_redblack_poly_io_insertions),
  ("dirprover_redblack_poly_mar_ser_io_insertions", dirprover_redblack_poly_mar_ser_io_insertions),
  ("prover_io_redblack_insertions", prover_io_redblack_insertions),
  ("dirverifier_redblack_io_insertions", dirverifier_redblack_io_insertions),
  ("dirverifier_redblack_poly_io_insertions", dirverifier_redblack_poly_io_insertions),
  ("dirverifier_redblack_poly_mar_ser_io_insertions", dirverifier_redblack_poly_mar_ser_io_insertions),
  ("verifier_io_redblack_insertions", verifier_io_redblack_insertions),
  ("lauth_prover_rb_insertions", lauth_prover_rb_insertions),
  ("lauth_verifier_rb_insertions", lauth_verifier_rb_insertions),
  ("dirprover_redblack_io_retrieves", dirprover_redblack_io_retrieves),
  ("dirprover_redblack_poly_io_retrieves", dirprover_redblack_poly_io_retrieves),
  ("dirprover_redblack_poly_mar_ser_io_retrieves", dirprover_redblack_poly_mar_ser_io_retrieves),
  ("prover_io_redblack_retrieves", prover_io_redblack_retrieves),
  ("dirverifier_redblack_io_retrieves", dirverifier_redblack_io_retrieves),
  ("dirverifier_redblack_poly_io_retrieves", dirverifier_redblack_poly_io_retrieves),
  ("dirverifier_redblack_poly_mar_ser_io_retrieves", dirverifier_redblack_poly_mar_ser_io_retrieves),
  ("verifier_io_redblack_retrieves", verifier_io_redblack_retrieves),
  ("lauth_prover_rb_retrieves", lauth_prover_rb_retrieves),
  ("lauth_verifier_rb_retrieves", lauth_verifier_rb_retrieves)
]
rb_indices = list(range(max(len(arr) for _, arr in rb_arrays)))
csv_path_rb = os.path.join(results_folder, "redblack_arrays.csv")
write_csv(csv_path_rb, rb_arrays, rb_indices)

# Merkle arrays (retrieves and updates)
merkle_arrays = [
  ("dirprover_merkle_io_retrieves", dirprover_merkle_io_retrieves),
  ("dirprover_merkle_poly_io_retrieves", dirprover_merkle_poly_io_retrieves),
  ("dirprover_merkle_poly_mar_ser_io_retrieves", dirprover_merkle_poly_mar_ser_io_retrieves),
  ("prover_io_merkle_retrieves", prover_io_merkle_retrieves),
  ("dirverifier_merkle_io_retrieves", dirverifier_merkle_io_retrieves),
  ("dirverifier_merkle_poly_io_retrieves", dirverifier_merkle_poly_io_retrieves),
  ("dirverifier_merkle_poly_mar_ser_io_retrieves", dirverifier_merkle_poly_mar_ser_io_retrieves),
  ("verifier_io_merkle_retrieves", verifier_io_merkle_retrieves),
  ("lauth_prover_merkle_retrieves", lauth_prover_merkle_retrieves),
  ("lauth_verifier_merkle_retrieves", lauth_verifier_merkle_retrieves),
  ("dirprover_merkle_io_updates", dirprover_merkle_io_updates),
  ("dirprover_merkle_poly_io_updates", dirprover_merkle_poly_io_updates),
  ("dirprover_merkle_poly_mar_ser_io_updates", dirprover_merkle_poly_mar_ser_io_updates),
  ("prover_io_merkle_updates", prover_io_merkle_updates),
  ("dirverifier_merkle_io_updates", dirverifier_merkle_io_updates),
  ("dirverifier_merkle_poly_io_updates", dirverifier_merkle_poly_io_updates),
  ("dirverifier_merkle_poly_mar_ser_io_updates", dirverifier_merkle_poly_mar_ser_io_updates),
  ("verifier_io_merkle_updates", verifier_io_merkle_updates),
  ("lauth_prover_merkle_updates", lauth_prover_merkle_updates),
  ("lauth_verifier_merkle_updates", lauth_verifier_merkle_updates)
]
merkle_indices = list(range(max(len(arr) for _, arr in merkle_arrays)))
csv_path_merkle = os.path.join(results_folder, "merkle_arrays.csv")
write_csv(csv_path_merkle, merkle_arrays, merkle_indices)
# # Write CSV files for redblack and merkle arrays with 5-digit float formatting
# def write_switched_csv(path, arrays, indices, header):
#   with open(path, "w", newline="") as csvfile:
#     writer = csv.writer(csvfile)
#     writer.writerow(["tree_size"] + [str(i+4) for i in indices])
#     for name, arr in arrays:
#       row = [name]
#       for i in indices:
#         v = arr[i] if i < len(arr) else ""
#         row.append(fmt(v) if v != "" else "")
#       writer.writerow(row)

# # Redblack arrays (insertions and retrieves)
# rb_arrays = [
#   ("dirprover_redblack_io_insertions", dirprover_redblack_io_insertions),
#   ("dirprover_redblack_poly_io_insertions", dirprover_redblack_poly_io_insertions),
#   ("dirprover_redblack_poly_mar_ser_io_insertions", dirprover_redblack_poly_mar_ser_io_insertions),
#   ("prover_io_redblack_insertions", prover_io_redblack_insertions),
#   ("dirverifier_redblack_io_insertions", dirverifier_redblack_io_insertions),
#   ("dirverifier_redblack_poly_io_insertions", dirverifier_redblack_poly_io_insertions),
#   ("dirverifier_redblack_poly_mar_ser_io_insertions", dirverifier_redblack_poly_mar_ser_io_insertions),
#   ("verifier_io_redblack_insertions", verifier_io_redblack_insertions),
#   ("lauth_prover_rb_insertions", lauth_prover_rb_insertions),
#   ("lauth_verifier_rb_insertions", lauth_verifier_rb_insertions),
#   ("dirprover_redblack_io_retrieves", dirprover_redblack_io_retrieves),
#   ("dirprover_redblack_poly_io_retrieves", dirprover_redblack_poly_io_retrieves),
#   ("dirprover_redblack_poly_mar_ser_io_retrieves", dirprover_redblack_poly_mar_ser_io_retrieves),
#   ("prover_io_redblack_retrieves", prover_io_redblack_retrieves),
#   ("dirverifier_redblack_io_retrieves", dirverifier_redblack_io_retrieves),
#   ("dirverifier_redblack_poly_io_retrieves", dirverifier_redblack_poly_io_retrieves),
#   ("dirverifier_redblack_poly_mar_ser_io_retrieves", dirverifier_redblack_poly_mar_ser_io_retrieves),
#   ("verifier_io_redblack_retrieves", verifier_io_redblack_retrieves),
#   ("lauth_prover_rb_retrieves", lauth_prover_rb_retrieves),
#   ("lauth_verifier_rb_retrieves", lauth_verifier_rb_retrieves)
# ]
# rb_indices = list(range(max(len(arr) for _, arr in rb_arrays)))
# csv_path_rb_switched = os.path.join(results_folder, "redblack_arrays.csv")
# write_switched_csv(csv_path_rb_switched, rb_arrays, rb_indices, None)

# # Merkle arrays (retrieves and updates)
# merkle_arrays = [
#   ("dirprover_merkle_io_retrieves", dirprover_merkle_io_retrieves),
#   ("dirprover_merkle_poly_io_retrieves", dirprover_merkle_poly_io_retrieves),
#   ("dirprover_merkle_poly_mar_ser_io_retrieves", dirprover_merkle_poly_mar_ser_io_retrieves),
#   ("prover_io_merkle_retrieves", prover_io_merkle_retrieves),
#   ("dirverifier_merkle_io_retrieves", dirverifier_merkle_io_retrieves),
#   ("dirverifier_merkle_poly_io_retrieves", dirverifier_merkle_poly_io_retrieves),
#   ("dirverifier_merkle_poly_mar_ser_io_retrieves", dirverifier_merkle_poly_mar_ser_io_retrieves),
#   ("verifier_io_merkle_retrieves", verifier_io_merkle_retrieves),
#   ("lauth_prover_merkle_retrieves", lauth_prover_merkle_retrieves),
#   ("lauth_verifier_merkle_retrieves", lauth_verifier_merkle_retrieves),
#   ("dirprover_merkle_io_updates", dirprover_merkle_io_updates),
#   ("dirprover_merkle_poly_io_updates", dirprover_merkle_poly_io_updates),
#   ("dirprover_merkle_poly_mar_ser_io_updates", dirprover_merkle_poly_mar_ser_io_updates),
#   ("prover_io_merkle_updates", prover_io_merkle_updates),
#   ("dirverifier_merkle_io_updates", dirverifier_merkle_io_updates),
#   ("dirverifier_merkle_poly_io_updates", dirverifier_merkle_poly_io_updates),
#   ("dirverifier_merkle_poly_mar_ser_io_updates", dirverifier_merkle_poly_mar_ser_io_updates),
#   ("verifier_io_merkle_updates", verifier_io_merkle_updates),
#   ("lauth_prover_merkle_updates", lauth_prover_merkle_updates),
#   ("lauth_verifier_merkle_updates", lauth_verifier_merkle_updates)
# ]
# merkle_indices = list(range(max(len(arr) for _, arr in merkle_arrays)))
# csv_path_merkle_switched = os.path.join(results_folder, "merkle_arrays.csv")
# write_switched_csv(csv_path_merkle_switched, merkle_arrays, merkle_indices, None)
