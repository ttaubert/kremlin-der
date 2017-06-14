#include "Test.h"

uint32_t Test_read_length(uint8_t *buf, uint32_t len)
{
  if (len == (uint32_t )0)
    return (uint32_t )0;
  else
  {
    uint32_t len1 = len - (uint32_t )1;
    uint8_t bi = buf[len1];
    uint32_t lo = (uint32_t )bi;
    uint32_t hi = Test_read_length(buf, len1);
    return hi << (uint32_t )8 | lo;
  }
}

bool Test_parse_len(uint8_t *buf, uint32_t len, uint32_t *out_len)
{
  uint8_t b0 = buf[0];
  uint8_t ilen = b0 & (uint8_t )0x7f;
  bool is_short_form = b0 == ilen;
  uint32_t ilen1 = (uint32_t )ilen;
  uint32_t res;
  if (is_short_form)
    res = ilen1;
  else
  {
    uint32_t ite0;
    if (ilen1 == (uint32_t )0)
      ite0 = (uint32_t )0;
    else
    {
      uint32_t ite1;
      if (ilen1 > (uint32_t )4)
        ite1 = (uint32_t )0;
      else
      {
        uint32_t ite;
        if (len <= ilen1)
          ite = (uint32_t )0;
        else
          ite = Test_read_length(buf + (uint32_t )1, ilen1);
        ite1 = ite;
      }
      ite0 = ite1;
    }
    res = ite0;
  }
  out_len[0] = res;
  return res > (uint32_t )0 || ilen1 == (uint32_t )0 && is_short_form;
}

