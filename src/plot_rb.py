import matplotlib.pyplot as plt
import statistics
import os

def get_times_lauth(s):
  sl = [i.split("+-") for i in s.split() if ("+-" in i)]
  return [1./float(i[0]) if "/s" in i[1] else float(i[0]) for i in sl]

results_folder = "results/"

auth_data_511 = open("results/auth_rb_511.txt").read()
auth_data_414 = open("results/auth_rb_414.txt").read()
auth_data_401 = open("results/auth_rb_401.txt").read()
lauthp_data = open("results/lauth_rb_prv.txt").read()
lauthv_data = open("results/lauth_rb_vrf.txt").read()

d_511 = {}
auth_times_511 = [line for line in auth_data_511.split("Profiling:\n")[1].split("\n")[:-1]]
for i in auth_times_511:
  s = i.split()
  if s[0] not in d_511:
    d_511[s[0]] = {}
  rest = " ".join(s[1:])
  size = int(rest.split(".")[0])
  times = [float(i) for i in sorted(s[-1].split("_")[:-1])]
  d_511[s[0]][size] = statistics.median(times)

d_414 = {}
auth_times_414 = [line for line in auth_data_414.split("Profiling:\n")[1].split("\n")[:-1]]
for i in auth_times_414:
  s = i.split()
  if s[0] not in d_414:
    d_414[s[0]] = {}
  rest = " ".join(s[1:])
  size = int(rest.split(".")[0])
  times = [float(i) for i in sorted(s[-1].split("_")[:-1])]
  d_414[s[0]][size] = statistics.median(times)

d_401 = {}
auth_times_401 = [line for line in auth_data_401.split("Profiling:\n")[1].split("\n")[:-1]]
for i in auth_times_401:
  s = i.split()
  if s[0] not in d_401:
    d_401[s[0]] = {}
  rest = " ".join(s[1:])
  size = int(rest.split(".")[0])
  times = [float(i) for i in sorted(s[-1].split("_")[:-1])]
  d_401[s[0]][size] = statistics.median(times)

direct_prover_redblack_insertions_511 = [d_511["direct_prover_redblack_insertions"][i] for i in range(4, 22)]
dirprover_redblack_io_insertions_511 = [d_511["dirprover_redblack_io_insertions"][i] for i in range(4, 22)]
dirprover_redblack_poly_io_insertions_511 = [d_511["dirprover_redblack_poly_io_insertions"][i] for i in range(4, 22)]
dirprover_redblack_poly_mar_ser_io_insertions_511 = [d_511["dirprover_redblack_poly_mar_ser_io_insertions"][i] for i in range(4, 22)]
prover_io_redblack_insertions_511 = [d_511["prover_io_redblack_insertions"][i] for i in range(4, 22)]
dirverifier_redblack_insertions_511 = [d_511["dirverifier_redblack_insertions"][i] for i in range(4, 22)]
dirverifier_redblack_io_insertions_511 = [d_511["dirverifier_redblack_io_insertions"][i] for i in range(4, 22)]
dirverifier_redblack_poly_io_insertions_511 = [d_511["dirverifier_redblack_poly_io_insertions"][i] for i in range(4, 22)]
dirverifier_redblack_poly_mar_ser_io_insertions_511 = [d_511["dirverifier_redblack_poly_mar_ser_io_insertions"][i] for i in range(4, 22)]
verifier_io_redblack_insertions_511 = [d_511["verifier_io_redblack_insertions"][i] for i in range(4, 22)]

direct_prover_redblack_insertions_414 = [d_414["direct_prover_redblack_insertions"][i] for i in range(4, 22)]
dirprover_redblack_io_insertions_414 = [d_414["dirprover_redblack_io_insertions"][i] for i in range(4, 22)]
dirprover_redblack_poly_io_insertions_414 = [d_414["dirprover_redblack_poly_io_insertions"][i] for i in range(4, 22)]
dirprover_redblack_poly_mar_ser_io_insertions_414 = [d_414["dirprover_redblack_poly_mar_ser_io_insertions"][i] for i in range(4, 22)]
prover_io_redblack_insertions_414 = [d_414["prover_io_redblack_insertions"][i] for i in range(4, 22)]
dirverifier_redblack_insertions_414 = [d_414["dirverifier_redblack_insertions"][i] for i in range(4, 22)]
dirverifier_redblack_io_insertions_414 = [d_414["dirverifier_redblack_io_insertions"][i] for i in range(4, 22)]
dirverifier_redblack_poly_io_insertions_414 = [d_414["dirverifier_redblack_poly_io_insertions"][i] for i in range(4, 22)]
dirverifier_redblack_poly_mar_ser_io_insertions_414 = [d_414["dirverifier_redblack_poly_mar_ser_io_insertions"][i] for i in range(4, 22)]
verifier_io_redblack_insertions_414 = [d_414["verifier_io_redblack_insertions"][i] for i in range(4, 22)]

direct_prover_redblack_insertions_401 = [d_401["direct_prover_redblack_insertions"][i] for i in range(4, 22)]
dirprover_redblack_io_insertions_401 = [d_401["dirprover_redblack_io_insertions"][i] for i in range(4, 22)]
dirprover_redblack_poly_io_insertions_401 = [d_401["dirprover_redblack_poly_io_insertions"][i] for i in range(4, 22)]
dirprover_redblack_poly_mar_ser_io_insertions_401 = [d_401["dirprover_redblack_poly_mar_ser_io_insertions"][i] for i in range(4, 22)]
prover_io_redblack_insertions_401 = [d_401["prover_io_redblack_insertions"][i] for i in range(4, 22)]
dirverifier_redblack_insertions_401 = [d_401["dirverifier_redblack_insertions"][i] for i in range(4, 22)]
dirverifier_redblack_io_insertions_401 = [d_401["dirverifier_redblack_io_insertions"][i] for i in range(4, 22)]
dirverifier_redblack_poly_io_insertions_401 = [d_401["dirverifier_redblack_poly_io_insertions"][i] for i in range(4, 22)]
dirverifier_redblack_poly_mar_ser_io_insertions_401 = [d_401["dirverifier_redblack_poly_mar_ser_io_insertions"][i] for i in range(4, 22)]
verifier_io_redblack_insertions_401 = [d_401["verifier_io_redblack_insertions"][i] for i in range(4, 22)]

lauth_prover = get_times_lauth(lauthp_data)
lauth_verifier = get_times_lauth(lauthv_data)

x = [i for i in range(4, 22)]

plt.rcParams['text.usetex'] = True
fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12, 3))
ax1.plot(x, prover_io_redblack_insertions_401, label='authentikit')
ax1.plot(x, dirprover_redblack_poly_mar_ser_io_insertions_401, label='authentikit-functor')
ax1.plot(x, dirprover_redblack_poly_io_insertions_401, label='authentikit-functor-prepare')
ax1.plot(x, dirprover_redblack_io_insertions_401, label='authentikit-functor-prepare-poly')
ax1.plot(x, direct_prover_redblack_insertions_401, label='authentikit-functor-prepare-poly-io')
ax1.plot(x, lauth_prover, label=r"$\lambda\bullet$")
ax1.set_xlabel("Tree size (log)")
ax1.set_title("Prover implementation ablation")

ax2.plot(x, verifier_io_redblack_insertions_401, label='authentikit')
ax2.plot(x, dirverifier_redblack_poly_mar_ser_io_insertions_401, label='authentikit-functor')
ax2.plot(x, dirverifier_redblack_poly_io_insertions_401, label='authentikit-functor-prepare')
ax2.plot(x, dirverifier_redblack_io_insertions_401, label='authentikit-functor-prepare-poly')
ax2.plot(x, dirverifier_redblack_insertions_401, label='authentikit-functor-prepare-poly-io')
ax2.plot(x, lauth_verifier, label=r"$\lambda\bullet$")
ax2.set_xlabel("Tree size (log)")
ax2.set_title("Verifier implementation ablation")

plt.legend(loc='upper center', bbox_to_anchor=(-0.12, -0.17), ncols=3)
fig.text(0.08, 0.5, 'Running time for 100,000 queries (s)', va='center', rotation='vertical')
plt.savefig("results/ablation_rb.png", bbox_inches='tight')


fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12, 3))
ax1.plot(x, prover_io_redblack_insertions_511, label='ocaml 5.1.1')
ax1.plot(x, prover_io_redblack_insertions_414, label='ocaml 4.14.2')
ax1.plot(x, prover_io_redblack_insertions_401, label='ocaml 4.01.0')
ax1.plot(x, lauth_prover, label=r"$\lambda\bullet$")
ax1.set_xlabel("Tree size (log)")
ax1.set_title("Prover implementation across versions")

ax2.plot(x, verifier_io_redblack_insertions_511, label='ocaml 5.1.1')
ax2.plot(x, verifier_io_redblack_insertions_414, label='ocaml 4.14.2')
ax2.plot(x, verifier_io_redblack_insertions_401, label='ocaml 4.01.0')
ax2.plot(x, lauth_verifier, label=r"$\lambda\bullet$")
ax2.set_xlabel("Tree size (log)")
ax2.set_title("Verifier implementation across versions")

plt.legend(loc='upper center', bbox_to_anchor=(-0.15, -0.17), ncols=4)
fig.text(0.08, 0.5, 'Running time for 100,000 queries (s)', va='center', rotation='vertical')
plt.savefig("results/versions_rb.png", bbox_inches='tight')


proofs_folder = f"data/4.01.0"
lauth_proof_folder = "../../lambda-auth/data/"

dirsizes = []
dirpolysizes = []
lauthsizes = []
for i in range(4, 22):
  size = os.path.getsize(f"{proofs_folder}/proof_rb_ins_d_{i:03d}.dat")
  dirsizes.append(size)

  size = os.path.getsize(f"{proofs_folder}/proof_rb_ins_dp_{i:03d}.dat")
  dirpolysizes.append(size)

  size = os.path.getsize(f"{lauth_proof_folder}/proof_rbp_ins_{i:03d}.dat")
  lauthsizes.append(size)

fig, ax = plt.subplots()
ax.plot(x, dirsizes, label='variants')
ax.plot(x, dirpolysizes, label='polymorphic variants')
ax.plot(x, lauthsizes, label='lambda-auth')
plt.xlabel("Tree size (log)")
plt.ylabel("Proof size for 100,000 queries (bytes)")
plt.legend()
plt.savefig("results/sizes_rb.png", bbox_inches='tight')
