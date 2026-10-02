project('campaign-next', 'cpp', version : '0.1.0',
  default_options : ['cpp_std=c++23', 'warning_level=2'])

json = dependency('nlohmann_json')
nxt = dependency('nxt')
nix = dependency('nix-main')
duckdb = meson.get_compiler('cpp').find_library('duckdb')

campaign = executable('filnix-campaign',
  ['src/main.cc', 'src/journal.cc', 'src/dataset.cc', 'src/web.cc'],
  dependencies : [nxt, json, duckdb], install : true)

executable('filnix-nix-worker', 'src/nix-worker.cc',
  cpp_args : ['-DNIX_LIBRARY_VERSION="' + nix.version() + '"'],
  dependencies : [nix, json], install : true)

install_data('static/htmx.js', 'static/HTMX-LICENSE',
  install_dir : get_option('datadir') / 'filnix-campaign')

dataset_test = executable('dataset-test',
  ['tests/test_dataset.cc', 'src/dataset.cc', 'src/journal.cc', 'src/web.cc'],
  include_directories : include_directories('src'),
  dependencies : [json, duckdb])
test('dataset', dataset_test)

python = find_program('python3')
test('campaign', python,
  args : [files('tests/test_campaign.py'), campaign.full_path()],
  env : {'CAMPAIGN_STATIC_DIR' : meson.current_source_dir() / 'static'},
  timeout : 90)
