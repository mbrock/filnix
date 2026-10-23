# Source licenses remain in each fetched tree (cproc: ISC, test/*:
# Unlicense; c-testsuite: per-test .otag provenance, not the runner's MIT).
{ pkgs }:
{
  cproc = pkgs.fetchzip {
    url = "https://codeload.github.com/michaelforney/cproc/tar.gz/d1c53ddf56571573a7025324c8dd5c6d547a4d1f";
    extension = "tar.gz";
    hash = "sha256-u9zlMI0NOLUXCXtEWw/c8gOgqeH6yAq+ZIqIoywPitU=";
  };
  c-testsuite = pkgs.fetchzip {
    url = "https://codeload.github.com/c-testsuite/c-testsuite/tar.gz/5c7275656d751de0e68b2d340a95b5681858ed07";
    extension = "tar.gz";
    hash = "sha256-bKfdr7veh+UJvvlumm7vxRyP5uO9uelZziBsp30HbgU=";
  };
}
