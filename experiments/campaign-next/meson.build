project('campaign-next', 'cpp', version : '0.1.0',
  default_options : ['cpp_std=c++23', 'warning_level=2'])

json = dependency('nlohmann_json')
nxt = dependency('nxt')
nix = dependency('nix-main')

campaign = executable('filnix-campaign',
  ['src/main.cc', 'src/journal.cc'],
  dependencies : [nxt, json], install : true)

executable('filnix-nix-worker', 'src/nix-worker.cc',
  cpp_args : ['-DNIX_LIBRARY_VERSION="' + nix.version() + '"'],
  dependencies : [nix, json], install : true)

python = find_program('python3')
test('campaign', python,
  args : [files('tests/test_campaign.py'), campaign.full_path()],
  timeout : 90)
