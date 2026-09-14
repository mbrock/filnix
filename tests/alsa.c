#include <alsa/asoundlib.h>
#include <assert.h>
#include <string.h>

int main(void)
{
    snd_pcm_t *pcm;
    short samples[256 * 2] = {0};
    /* This public entry point is one of ALSA's weak symbol aliases. */
    assert(strcmp(snd_pcm_type_name(SND_PCM_TYPE_NULL), "NULL") == 0);
    assert(snd_pcm_open(&pcm, "null", SND_PCM_STREAM_PLAYBACK, 0) == 0);
    assert(snd_pcm_set_params(pcm, SND_PCM_FORMAT_S16_LE,
                             SND_PCM_ACCESS_RW_INTERLEAVED,
                             2, 48000, 0, 100000) == 0);
    assert(snd_pcm_writei(pcm, samples, 256) == 256);
    assert(snd_pcm_drain(pcm) == 0);
    assert(snd_pcm_close(pcm) == 0);
    return 0;
}
