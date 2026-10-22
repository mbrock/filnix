# Nixpkgs' redis test (nixos/tests/redis.nix) builds with the old
# make-test-python and can't be imported as a module; this is its machine
# and script, with the client from the server's own package.
{ ... }:
{
  name = "redis";
  nodes.machine =
    { config, lib, ... }:
    {
      services.redis.servers."".enable = true;
      services.redis.servers."test".enable = true;
      users.users =
        lib.mapAttrs
          (_: group: {
            isNormalUser = true;
            extraGroups = [ group ];
          })
          {
            member = "redis";
            member-test = "redis-test";
          };
      environment.systemPackages = [ config.services.redis.package ];
    };

  testScript =
    { nodes, ... }:
    let
      inherit (nodes.machine.services.redis) servers;
    in
    ''
      machine.wait_for_unit("redis")
      machine.wait_for_unit("redis-test")
      machine.wait_for_open_port(6379)
      machine.wait_for_file("${servers."".unixSocket}")
      machine.wait_for_file("${servers."test".unixSocket}")

      # The unix sockets are accessible to the redis groups.
      machine.succeed('su member -c "redis-cli -s ${servers."".unixSocket} ping | grep PONG"')
      machine.succeed('su member-test -c "redis-cli -s ${servers."test".unixSocket} ping | grep PONG"')

      machine.succeed("redis-cli ping | grep PONG")
      machine.succeed("redis-cli set greeting hello")
      machine.succeed("redis-cli get greeting | grep hello")
    '';
}
