/* Locale loading against a glibc that may be stock (unpatched) or
   patched (patches/filc-glibc-loadarchive-validate.patch,
   filc-glibc-loadlocale-validate.patch).  The archive loader trusts
   the offsets, lengths and counts stored in the locale-archive file,
   and the category loader trusts the index stored in each locale
   file, so a truncated or inconsistent file sends a stock loader past
   its mapping or around an unbounded probe loop.  Each mode writes
   its crafted file, points the loader at it and calls setlocale.
   A patched loader refuses the file and the mode prints "rejected"
   and exits zero; a stock loader faults on the bad read (or spins, in
   the full-table mode) and the mode dies or hangs instead, which the
   caller (regress.nix) reports.  Two valid modes must load under
   both loaders: the control tree, and a well-formed one-entry
   archive built from the control tree's own monetary data.

   The corrupt modes place their bad reads past the file's last page
   on purpose.  Fil-C bounds an mmap by whole pages, so a read a few
   bytes past a short file stays inside the zero-filled page tail,
   while a read past the final page faults for real.  Every crafted
   file is therefore a whole page, so the same bytes fault on every
   run.

   Usage: locarch CONTROL-LOCALE-DIR WORKDIR MODE

   CONTROL-LOCALE-DIR is a locale tree (a glibc's lib/locale) with
   C.utf8 in it; WORKDIR receives the crafted files. */
#include <errno.h>
#include <locale.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>

#define PAGE 4096
#define LC_MONETARY_IDX 4
#define NRECORDS 13
#define HEAD_BYTES 56
#define NHENT_BYTES 12
#define LOCREC_BYTES (4 + NRECORDS * 8)

/* The archive loader's hash, as loadarchive.c defines it over
   hashval_t = uint32_t (locale/hashval.h). */
static unsigned int
probe_hash (const char *key)
{
  size_t len = strlen (key);
  unsigned int hval = (unsigned int) len;
  for (size_t i = 0; i < len; i++)
    hval = (hval << 9) | (hval >> 23), hval += (unsigned char) key[i];
  return hval ? hval : 0xffffffffu;
}

static void
put32 (unsigned char *p, size_t off, unsigned int v)
{
  p[off] = (unsigned char) v;
  p[off + 1] = (unsigned char) (v >> 8);
  p[off + 2] = (unsigned char) (v >> 16);
  p[off + 3] = (unsigned char) (v >> 24);
}

static void
put_str (unsigned char *p, size_t off, const char *s)
{
  memcpy (p + off, s, strlen (s) + 1);
}

/* A locarhead: magic, serial, then the table offsets and sizes, all
   uint32.  The loader never checks the magic. */
static void
head_init (unsigned char *p)
{
  memset (p, 0, PAGE);
  put32 (p, 0, 0xde020109u); /* AR_MAGIC */
  put32 (p, 4, 1);           /* serial */
  put32 (p, 8, HEAD_BYTES);  /* namehash_offset */
  put32 (p, 20, 92);         /* string_offset */
  put32 (p, 28, 64);         /* string_size */
  put32 (p, 32, 100);        /* locrectab_offset */
  put32 (p, 44, 208);        /* sumhash_offset */
}

static void
slot_set (unsigned char *p, unsigned int idx, unsigned int hashval,
          unsigned int name_offset, unsigned int locrec_offset)
{
  size_t off = HEAD_BYTES + (size_t) idx * NHENT_BYTES;
  put32 (p, off, hashval);
  put32 (p, off + 4, name_offset);
  put32 (p, off + 8, locrec_offset);
}

/* The locale record lives at locrectab_offset, aligned the way
   localedef writes it (the loader reads it as struct locrecent).  */
static void
record_set (unsigned char *p, unsigned int cat, unsigned int offset,
            unsigned int len)
{
  put32 (p, 100 + 4 + (size_t) cat * 8, offset);
  put32 (p, 100 + 4 + (size_t) cat * 8 + 4, len);
}

static int
write_file (const char *path, const unsigned char *buf, size_t len)
{
  FILE *f = fopen (path, "w");
  if (f == NULL)
    return -1;
  if (fwrite (buf, 1, len, f) != len)
    {
      fclose (f);
      return -1;
    }
  return fclose (f);
}

static int
mkdirs (const char *path)
{
  char buf[512];
  snprintf (buf, sizeof buf, "%s", path);
  for (char *p = strchr (buf + 1, '/'); p; p = strchr (p + 1, '/'))
    {
      *p = 0;
      mkdir (buf, 0777);
      *p = '/';
    }
  return mkdir (buf, 0777) == 0 || errno == EEXIST ? 0 : -1;
}

static void
path_of (char *out, size_t n, const char *work, const char *name)
{
  snprintf (out, n, "%s/%s", work, name);
}

static const char *
locpath_dir (const char *work)
{
  static char dir[512];
  snprintf (dir, sizeof dir, "%s/locpath", work);
  return dir;
}

/* The control tree's monetary file: the valid modes' archive blob and
   the base of the crafted category files. */
static unsigned char mon[PAGE];
static size_t mon_len;
static unsigned int mon_nstrings;

static int
read_monetary (const char *control_dir)
{
  char path[512];
  FILE *f;
  snprintf (path, sizeof path, "%s/C.utf8/LC_MONETARY", control_dir);
  f = fopen (path, "r");
  if (f == NULL)
    return -1;
  mon_len = fread (mon, 1, sizeof mon, f);
  fclose (f);
  mon_nstrings = ((unsigned int) mon[4] | ((unsigned int) mon[5] << 8)
                  | ((unsigned int) mon[6] << 16)
                  | ((unsigned int) mon[7] << 24));
  /* The monetary blob goes at offset 208 of the crafted archive, so
     it, and the record that points at it, must leave room for the
     header in the page. */
  return mon_len > 8 + (size_t) mon_nstrings * 4
    && mon_len <= sizeof mon - 512
    && mon_nstrings > 0 && mon_nstrings < 256 ? 0 : -1;
}

static void
use_archive (const char *path)
{
  unsetenv ("LOCPATH");
  unsetenv ("LOCALE_ARCHIVE_2_27");
  setenv ("LOCALE_ARCHIVE", path, 1);
}

static void
use_locpath (const char *dir)
{
  unsetenv ("LOCALE_ARCHIVE");
  unsetenv ("LOCALE_ARCHIVE_2_27");
  setenv ("LOCPATH", dir, 1);
}

/* Reads the loaded monetary values, so a locale that loads but points
   out of its file faults here rather than passing silently. */
static int
print_monetary (void)
{
  struct lconv *l = localeconv ();
  printf ("monetary: %s|%s|%d\n", l->int_curr_symbol,
          l->mon_decimal_point, l->int_frac_digits);
  return 0;
}

static unsigned char buf[PAGE];

static void
must_write (const char *mode, const char *path, size_t len)
{
  if (write_file (path, buf, len) != 0)
    {
      printf ("%s: write failed\n", mode);
      exit (2);
    }
}

/* Load the control tree the plain way. */
static int
mode_control (const char *control_dir, const char *work)
{
  (void) work;
  use_locpath (control_dir);
  if (setlocale (LC_ALL, "C.utf8") == NULL)
    {
      printf ("control: setlocale failed\n");
      return 1;
    }
  printf ("control: ok ");
  return print_monetary ();
}

/* A well-formed one-entry archive.  Its monetary blob is the control
   tree's own file, so this must load under a patched loader and print
   the control mode's values; a patched loader must not refuse good
   archives. */
static int
mode_archive_valid (const char *control_dir, const char *work)
{
  char path[512];
  unsigned int hval = probe_hash ("probe");
  unsigned int slot = hval % 3;
  (void) control_dir;
  path_of (path, sizeof path, work, "valid");
  head_init (buf);
  put32 (buf, 12, 1);  /* namehash_used */
  put32 (buf, 16, 3);  /* namehash_size */
  put32 (buf, 24, 6);  /* string_used: "probe" */
  put32 (buf, 36, 1);  /* locrectab_used */
  put32 (buf, 40, 1);  /* locrectab_size */
  slot_set (buf, slot, hval, 92, 100);
  put_str (buf, 92, "probe");
  put32 (buf, 100, 1); /* locrecent refs */
  record_set (buf, LC_MONETARY_IDX, 208, (unsigned int) mon_len);
  memcpy (buf + 208, mon, mon_len);
  must_write ("archive-valid", path, PAGE);
  use_archive (path);
  if (setlocale (LC_MONETARY, "probe") == NULL)
    {
      printf ("archive-valid: setlocale failed\n");
      return 1;
    }
  printf ("archive-valid: ok ");
  return print_monetary ();
}

/* A hash table with no matching entry and no empty slot.  Unpatched,
   the probe loop has nothing to stop it and spins; patched, it stops
   after namehash_size probes and refuses the load. */
static int
mode_archive_loop (const char *control_dir, const char *work)
{
  char path[512];
  unsigned int hval = probe_hash ("probe");
  (void) control_dir;
  path_of (path, sizeof path, work, "loop");
  head_init (buf);
  put32 (buf, 12, 8);   /* namehash_used */
  put32 (buf, 16, 8);   /* namehash_size */
  put32 (buf, 20, 152); /* string_offset */
  put32 (buf, 24, 64);  /* string_used: eight "nope<N>" names */
  put32 (buf, 32, 216); /* locrectab_offset */
  put32 (buf, 36, 1);   /* locrectab_used */
  for (unsigned int i = 0; i < 8; i++)
    {
      char name[8];
      snprintf (name, sizeof name, "nope%u", i);
      put_str (buf, 152 + i * 8, name);
      slot_set (buf, i, hval ^ (i + 1), 152 + i * 8, 216);
    }
  must_write ("archive-loop", path, PAGE);
  use_archive (path);
  if (setlocale (LC_MONETARY, "probe") != NULL)
    {
      printf ("archive-loop: loaded\n");
      return 1;
    }
  printf ("archive-loop: rejected\n");
  return 0;
}

/* An entry whose name is not NUL-terminated inside the file: the name
   ends exactly at the last page, so unpatched strcmp faults reading
   its terminating NUL; patched, an entry name needs a NUL inside the
   string table. */
static int
mode_archive_nonul (const char *control_dir, const char *work)
{
  char path[512];
  unsigned int hval = probe_hash ("abc");
  unsigned int slot = hval % 3;
  (void) control_dir;
  path_of (path, sizeof path, work, "nonul");
  head_init (buf);
  put32 (buf, 12, 1);    /* namehash_used */
  put32 (buf, 16, 3);    /* namehash_size */
  put32 (buf, 20, 4093); /* string_offset */
  put32 (buf, 24, 3);    /* string_used: "abc" without its NUL */
  slot_set (buf, slot, hval, 4093, 0);
  buf[4093] = 'a'; buf[4094] = 'b'; buf[4095] = 'c';
  must_write ("archive-nonul", path, PAGE);
  use_archive (path);
  if (setlocale (LC_MONETARY, "abc") != NULL)
    {
      printf ("archive-nonul: loaded\n");
      return 1;
    }
  printf ("archive-nonul: rejected\n");
  return 0;
}

/* An entry whose name points outside the mapping. */
static int
mode_archive_name_oob (const char *control_dir, const char *work)
{
  char path[512];
  unsigned int hval = probe_hash ("abc");
  unsigned int slot = hval % 3;
  (void) control_dir;
  path_of (path, sizeof path, work, "name-oob");
  head_init (buf);
  put32 (buf, 12, 1);  /* namehash_used */
  put32 (buf, 16, 3);  /* namehash_size */
  put32 (buf, 24, 6);  /* string_used: "probe" */
  put_str (buf, 92, "probe");
  slot_set (buf, slot, hval, 0x7ffffff0u, 0);
  must_write ("archive-name-oob", path, PAGE);
  use_archive (path);
  if (setlocale (LC_MONETARY, "abc") != NULL)
    {
      printf ("archive-name-oob: loaded\n");
      return 1;
    }
  printf ("archive-name-oob: rejected\n");
  return 0;
}

/* A matching entry whose locale record starts four bytes before the
   end of the file: unpatched, the record loop reads its fields past
   the last page; patched, a locale record must fit inside the
   mapping. */
static int
mode_archive_locrec_oob (const char *control_dir, const char *work)
{
  char path[512];
  unsigned int hval = probe_hash ("probe");
  unsigned int slot = hval % 3;
  (void) control_dir;
  path_of (path, sizeof path, work, "locrec-oob");
  head_init (buf);
  put32 (buf, 12, 1);  /* namehash_used */
  put32 (buf, 16, 3);  /* namehash_size */
  put32 (buf, 24, 6);  /* string_used: "probe" */
  slot_set (buf, slot, hval, 92, PAGE - 4);
  put_str (buf, 92, "probe");
  must_write ("archive-locrec-oob", path, PAGE);
  use_archive (path);
  if (setlocale (LC_MONETARY, "probe") != NULL)
    {
      printf ("archive-locrec-oob: loaded\n");
      return 1;
    }
  printf ("archive-locrec-oob: rejected\n");
  return 0;
}

/* A record whose offset + len wraps in 32 bits: 0xffffff00 + 0x100.
   Unpatched, the bound check sums the uint32 fields in 32 bits, the
   record passes, and loading it reads at 4 GB past the mapping;
   patched, the sum is 64-bit and the record is refused. */
static int
mode_archive_record_wrap (const char *control_dir, const char *work)
{
  char path[512];
  unsigned int hval = probe_hash ("probe");
  unsigned int slot = hval % 3;
  (void) control_dir;
  path_of (path, sizeof path, work, "record-wrap");
  head_init (buf);
  put32 (buf, 12, 1);  /* namehash_used */
  put32 (buf, 16, 3);  /* namehash_size */
  put32 (buf, 24, 6);  /* string_used: "probe" */
  put32 (buf, 36, 1);  /* locrectab_used */
  slot_set (buf, slot, hval, 92, 100);
  put_str (buf, 92, "probe");
  put32 (buf, 100, 1); /* locrecent refs */
  record_set (buf, LC_MONETARY_IDX, 0xffffff00u, 0x100);
  must_write ("archive-record-wrap", path, PAGE);
  use_archive (path);
  if (setlocale (LC_MONETARY, "probe") != NULL)
    {
      printf ("archive-record-wrap: loaded\n");
      return 1;
    }
  printf ("archive-record-wrap: rejected\n");
  return 0;
}

/* A monetary file, loaded through LOCPATH so _nl_intern_locale_data
   reads it, whose strindex entries all point exactly at the end of
   the file.  Unpatched, idx == filesize passes the idx > filesize
   check and the first word value reads its four bytes past the last
   page; patched, an index must point strictly inside the file. */
static int
mode_file_idx_eof (const char *control_dir, const char *work)
{
  char dir[512], path[512];
  (void) control_dir;
  snprintf (dir, sizeof dir, "%s/locpath/probe", work);
  if (mkdirs (dir) != 0)
    {
      printf ("file-idx-eof: mkdir failed\n");
      return 1;
    }
  snprintf (path, sizeof path, "%s/LC_MONETARY", dir);
  memset (buf, 'a', PAGE);
  memcpy (buf, mon, 8); /* magic and nstrings of the real file */
  for (unsigned int i = 0; i < mon_nstrings; i++)
    put32 (buf, 8 + i * 4, PAGE);
  must_write ("file-idx-eof", path, PAGE);
  use_locpath (locpath_dir (work));
  if (setlocale (LC_MONETARY, "probe") != NULL)
    {
      printf ("file-idx-eof: loaded\n");
      print_monetary ();
      return 1;
    }
  printf ("file-idx-eof: rejected\n");
  return 0;
}

/* A monetary file whose first string is not NUL-terminated: it starts
   four bytes before the end of the file.  Unpatched, setlocale
   succeeds and reading the string (int_curr_symbol) faults past the
   last page; patched, a string needs a NUL inside the file. */
static int
mode_file_nonul (const char *control_dir, const char *work)
{
  char dir[512], path[512];
  (void) control_dir;
  snprintf (dir, sizeof dir, "%s/locpath/probe", work);
  if (mkdirs (dir) != 0)
    {
      printf ("file-nonul: mkdir failed\n");
      return 1;
    }
  snprintf (path, sizeof path, "%s/LC_MONETARY", dir);
  memset (buf, 'a', PAGE);
  memcpy (buf, mon, 8); /* magic and nstrings of the real file */
  for (unsigned int i = 0; i < mon_nstrings; i++)
    put32 (buf, 8 + i * 4, 192);
  put32 (buf, 8, PAGE - 4);
  buf[PAGE - 4] = 'a'; buf[PAGE - 3] = 'b';
  buf[PAGE - 2] = 'c'; buf[PAGE - 1] = 'd';
  must_write ("file-nonul", path, PAGE);
  use_locpath (locpath_dir (work));
  if (setlocale (LC_MONETARY, "probe") == NULL)
    {
      printf ("file-nonul: rejected\n");
      return 0;
    }
  printf ("file-nonul: loaded ");
  print_monetary ();
  return 1;
}

int
main (int argc, char **argv)
{
  const char *mode;
  if (argc != 4)
    {
      printf ("usage: locarch CONTROL-LOCALE-DIR WORKDIR MODE\n");
      return 2;
    }
  if (read_monetary (argv[1]) != 0)
    {
      printf ("locarch: cannot read %s/C.utf8/LC_MONETARY\n", argv[1]);
      return 2;
    }
  mode = argv[3];
  if (strcmp (mode, "control") == 0)
    return mode_control (argv[1], argv[2]);
  if (strcmp (mode, "archive-valid") == 0)
    return mode_archive_valid (argv[1], argv[2]);
  if (strcmp (mode, "archive-loop") == 0)
    return mode_archive_loop (argv[1], argv[2]);
  if (strcmp (mode, "archive-nonul") == 0)
    return mode_archive_nonul (argv[1], argv[2]);
  if (strcmp (mode, "archive-name-oob") == 0)
    return mode_archive_name_oob (argv[1], argv[2]);
  if (strcmp (mode, "archive-locrec-oob") == 0)
    return mode_archive_locrec_oob (argv[1], argv[2]);
  if (strcmp (mode, "archive-record-wrap") == 0)
    return mode_archive_record_wrap (argv[1], argv[2]);
  if (strcmp (mode, "file-idx-eof") == 0)
    return mode_file_idx_eof (argv[1], argv[2]);
  if (strcmp (mode, "file-nonul") == 0)
    return mode_file_nonul (argv[1], argv[2]);
  printf ("locarch: unknown mode %s\n", mode);
  return 2;
}
