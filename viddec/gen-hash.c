/*
 * Copyright (c) 2015 Ludmila Glinskih
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */

/**
 * H264 codec test.
 */
#include <stdio.h>
#include <assert.h>
#include <stdlib.h>
#include <time.h>
#include <stdint.h>
#include <stdbool.h>
#include <string.h>

#include "libavutil/adler32.h"
#include "libavcodec/avcodec.h"
#include "libavformat/avformat.h"
#include "libavutil/imgutils.h"
#include "libavutil/timestamp.h"
#include "libavutil/base64.h"

AVFormatContext* fmt_ctx;
int frame_offset = 0;
int macroblock_offset = 0;
int region_width = 32;
int region_height = 32;

int ffmpeg_videoStreamIndex;
AVBitStreamFilterContext* h264bsfc = NULL;

static long privateId = 0;
AVDictionary *frameDict = NULL;

bool ARG_QUIET, ARG_HELP;
const char* ARG_VIDEO_PATH;
void parse_options(int argc, const char* argv[]);
void hexDump (unsigned char *pData, int n);
static char* itoa(int val, int base);
int getParam(AVFrame *frame, char *key);
int extractLuma(AVFrame *frame, unsigned char *pRawY, int x , int y, int width, int height);

char *mb_data = NULL;
int mb_size = 0;
void parse_options(int argc, const char* argv[])
{
	int i = 1;
	while(i < argc)
	{
		if(strcmp(argv[i], "--help") == 0 || strcmp(argv[i], "-h") == 0)
			ARG_HELP = true;
		else if(strcmp(argv[i], "-q") == 0 || strcmp(argv[i], "--quiet") == 0)
			ARG_QUIET = true;
		else if(strcmp(argv[i], "-f") == 0 || strcmp(argv[i], "--frame") == 0) {
			if(i+1 < argc)
				frame_offset = atoi(argv[i+1]);
			i++;
		} else if(strcmp(argv[i], "-m") == 0 || strcmp(argv[i], "--macroblock") == 0){
			if(i+1 < argc)
				macroblock_offset = atoi(argv[i+1]);
			i++;
		}else {
			ARG_VIDEO_PATH = argv[i];
		}
		i++;
	}
	if(ARG_HELP || ARG_VIDEO_PATH == NULL)
	{
		fprintf(stderr, "Usage: gen-hash [--frame] [--macroblock] videoPath\n  --help and -h will output this help message.\n   --frame frame offset.\n  --macroblock macroblock offset.\n");
		exit(1);
	}
}

void hexDump (unsigned char *pData, int n)
{
	for (int i=0; i< n; i++) {
		printf("%02x ", pData[i]);
	}
	printf("\n");
}

static char* itoa(int val, int base){

	static char buf[32] = {0};
	int i = 30;

	for(; val && i ; --i, val /= base)
		buf[i] = "0123456789abcdef"[val % base];

	return &buf[i+1];
}

int getParam(AVFrame *frame, char *key)
{
	AVDictionaryEntry *ent = av_dict_get(frame->metadata,key, NULL, 0);
	if(ent) {
		char *value = ent->value;
		if(value) {
			int intValue = atoi(value);
			printf("getParam key=%s value=%s 0x%0x\n", key, value, intValue);
			return intValue;
		}
	}
	return -1;
}

int extractLuma(AVFrame *frame, unsigned char *pRawY, int x , int y, int width, int height)
{
	unsigned char *pDst = pRawY;
	if((x + width) > frame->linesize[0] || (y + height) > frame->height)
		return -1;
	for (int v=0; v < height; v++){
		char *pSrc = frame->data[0] + (y + v)  * frame->linesize[0] + x;
		for (int w=0; w < width; w++){
			*pDst++ = *pSrc++;
		}
	}
	return 0;
}

int main(int argc, char **argv)
{
    AVFrame *frame = NULL;
    AVPacket *pkt;
    uint8_t inbuf[1024];
    int frame_count = 0;
	av_register_all();
	parse_options(argc, argv);

	pkt = (AVPacket *)av_malloc(sizeof(AVPacket));

	int idr_frame = -1;

    if (argc < 2) {
        av_log(NULL, AV_LOG_ERROR, "Incorrect input\n");
        return 1;
    }

    //if (video_decode_example(argv[1]) != 0)
    //    return 1;
    AVCodec *codec = avcodec_find_decoder(AV_CODEC_ID_H264);
    if (!codec) {
    	fprintf(stderr, "Codec not found\n");
    	exit(1);
    } else {
    	fprintf(stderr, "Codec found\n");
    }
    if (!frame) {
    	if (!(frame = av_frame_alloc())) {
    		fprintf(stderr, "Could not allocate frame\n");
    			exit(1);
    	}
	}

    AVCodecContext *c = avcodec_alloc_context3(codec);
    if (!c) {
    	fprintf(stderr, "Could not allocate audio codec context\n");
    	exit(1);
	}
    /* open it */
    if (avcodec_open2(c, codec, NULL) < 0) {
    	fprintf(stderr, "Could not open codec\n");
    	exit(1);
    }


	fmt_ctx = avformat_alloc_context();
	ffmpeg_videoStreamIndex = -1;

	int err = 0;

	if ((err = avformat_open_input(&fmt_ctx, ARG_VIDEO_PATH, NULL, NULL)) != 0) {
		fprintf(stderr, "Couldn't open file. Possibly it doesn't exist.");
		exit(1);
	}

	if ((err = avformat_find_stream_info(fmt_ctx, NULL)) < 0) {
		fprintf(stderr, "Stream information not found.");
		exit(1);
	}

	for(int i = 0; i < fmt_ctx->nb_streams; i++) {
		AVCodecContext *codec_ctx = fmt_ctx->streams[i]->codec;
		if( AVMEDIA_TYPE_VIDEO == codec_ctx->codec_type && ffmpeg_videoStreamIndex < 0 ) {
			AVCodec *pCodec = avcodec_find_decoder(codec_ctx->codec_id);
			AVDictionary *opts = NULL;

			ffmpeg_videoStreamIndex = i;
			if (codec_ctx->codec_id == AV_CODEC_ID_H264) {
			    if (codec_ctx->codec_id == AV_CODEC_ID_H264)
			        h264bsfc = av_bitstream_filter_init("h264_mp4toannexb");
			}
			break;
		}
	}

	if(ffmpeg_videoStreamIndex == -1){
		fprintf(stderr, "Video stream not found.");
	}
	unsigned char *pRawY = malloc(region_width * region_height);

	while(av_read_frame(fmt_ctx, pkt) >= 0) {
		if (pkt && pkt->size && ffmpeg_videoStreamIndex == pkt->stream_index) {
			if (h264bsfc) {
				av_bitstream_filter_filter(h264bsfc, fmt_ctx->streams[ffmpeg_videoStreamIndex]->codec, NULL, &pkt->data, &pkt->size, pkt->data, pkt->size, 0);
				hexDump(pkt->data, 16);
				//read_debug_nal_unit(h, pkt->data + 4, pkt->size - 4);
			    uint8_t* p = pkt->data;
			    size_t sz = pkt->size;
				int nal_start, nal_end, nalu_type;

				av_frame_unref(frame);
				int got_frame = 0;


				int ret = avcodec_decode_video2(c, frame, &got_frame, pkt);
				if (ret < 0) {
					fprintf(stderr, "Failed to decode\n");
					exit(1);
				} else if (got_frame){
					fprintf(stderr, "Frame decoded\n");
					if(frame_count == frame_offset) {
						extractLuma(frame, pRawY, 0, 0, region_width, region_height);
						break;
					}
					frame_count++;
				}
			}
		}
	    av_packet_unref(pkt);
	}
	free(mb_data);
	free (pRawY);
    return 0;

}
