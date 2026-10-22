/* After a collection, FUGC asks the scavenger to keep the pages that
   collection's sweep freed until the next collection, for at most
   FUGC_SCAVENGE_HOLD_MS (default 10 s). Allocate and drop ~256 MB and
   collect once: one second later RSS must still be up (without the hold the
   scavenger returns it within ~0.5 s), and once the hold lapses with the
   program idle, RSS must come back down. Run with FUGC_SCAVENGE_HOLD_MS=3000. */
#include <stdfil.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#define CHUNKS (256 * 1024)
#define CHUNK 1024

static char **chunks;

static long rss_mb(void)
{
    FILE *f = fopen("/proc/self/statm", "r");
    long size, resident;
    if (!f || fscanf(f, "%ld %ld", &size, &resident) != 2) {
        printf("FAIL statm\n");
        exit(1);
    }
    fclose(f);
    return resident * sysconf(_SC_PAGESIZE) / (1024 * 1024);
}

static void churn(void)
{
    chunks = malloc(CHUNKS * sizeof(char *));
    for (int i = 0; i < CHUNKS; i++) {
        chunks[i] = malloc(CHUNK);
        memset(chunks[i], i, CHUNK);
    }
    for (int i = 0; i < CHUNKS; i++)
        chunks[i] = NULL;
    free(chunks);
    chunks = NULL;
}

int main(void)
{
    long before = rss_mb();
    churn();
    long peak = rss_mb();
    zgc_request_and_wait();
    long after_gc = rss_mb();
    printf("rss before %ld MB, peak %ld MB, after gc %ld MB\n", before, peak, after_gc);
    if (peak - before < 128) {
        printf("FAIL churn did not grow RSS\n");
        return 1;
    }
    sleep(1);
    long held = rss_mb();
    printf("rss 1 s after gc %ld MB\n", held);
    if (held - before < (peak - before) / 2) {
        printf("FAIL scavenger did not hold the swept pages\n");
        return 1;
    }
    /* The hold lapses after FUGC_SCAVENGE_HOLD_MS; then pages older than
       the scavenger's 300 ms age limit go back on its 125 ms period. */
    for (int t = 0; t < 300; t++) {
        long now = rss_mb();
        if (now - before < (peak - before) / 2) {
            printf("rss back to %ld MB after %d00 ms idle\n", now, 10 + t);
            printf("scavenge hold ok\n");
            return 0;
        }
        usleep(100000);
    }
    printf("FAIL rss stuck at %ld MB\n", rss_mb());
    return 1;
}
