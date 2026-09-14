/* Installed SDL must discover the virtual sink through its PipeWire backend. */
#ifdef SDL_THREE
#include <SDL3/SDL.h>
#else
#include <SDL.h>
#endif
#include <assert.h>
#include <stdio.h>
#include <string.h>

int main(int argc, char **argv)
{
    assert(argc == 2);
    FILE *maps = fopen("/proc/self/maps", "r");
    assert(maps);
    char line[4096];
    int found = 0;
    while (fgets(line, sizeof(line), maps)) {
        if (strstr(line, "/lib/libc.so.6666")) {
            assert(strstr(line, argv[1]));
            ++found;
        }
    }
    fclose(maps);
    assert(found);
#ifdef SDL_THREE
    assert(SDL_Init(SDL_INIT_AUDIO));
    int count;
    SDL_AudioDeviceID *devices = SDL_GetAudioPlaybackDevices(&count);
    assert(devices && count > 0);
    assert(SDL_GetAudioDeviceName(devices[0]));
    SDL_free(devices);
#else
    assert(SDL_Init(SDL_INIT_AUDIO) == 0);
    assert(SDL_GetNumAudioDevices(0) > 0);
    assert(SDL_GetAudioDeviceName(0, 0));
#endif
    assert(!strcmp(SDL_GetCurrentAudioDriver(), "pipewire"));
    SDL_Quit();
    printf("SDL%d: shared libc and live PipeWire device discovery passed\n",
           SDL_MAJOR_VERSION);
    return 0;
}
