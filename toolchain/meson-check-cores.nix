# Meson concurrency alone does not bound tests that size their own thread pools
# from sched_getaffinity(). Keep both within this build's Nix core allocation.
{ pkgs }:
old: {
  preCheck = (old.preCheck or "") + ''
    export FUGC_THREADS="$NIX_BUILD_CORES"
    filcTestCpus=$(${pkgs.python3}/bin/python3 -c '
    import os
    cpus = sorted(os.sched_getaffinity(0))
    cores = int(os.environ["NIX_BUILD_CORES"])
    print(",".join(map(str, cpus[:cores] if cores > 0 else cpus)))
    ')
    mesonCheckFlagsArray+=(--num-processes "$NIX_BUILD_CORES"
      --wrapper "${pkgs.util-linuxMinimal}/bin/taskset -c $filcTestCpus")
  '';
}
