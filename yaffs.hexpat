#include <std/sys.pat>
#include <std/mem.pat>
#include <std/time.pat>


enum yaffs_obj_type :u32 {
	YAFFS_OBJECT_TYPE_UNKNOWN,
	YAFFS_OBJECT_TYPE_FILE,
	YAFFS_OBJECT_TYPE_SYMLINK,
	YAFFS_OBJECT_TYPE_DIRECTORY,
	YAFFS_OBJECT_TYPE_HARDLINK,
	YAFFS_OBJECT_TYPE_SPECIAL
};

fn u32_to_file_mode(u32 m){
  return std::format("0o{:07o}", m);
};

fn u32_to_timestr(u32 e){
  std::time::Time t = std::time::to_local(e);
  return std::time::format(t, "%Y-%m-%d %H:%M:%S");
};

using u32_file_mode = u32[[format("u32_to_file_mode")]];
using u32_time_t = u32[[format("u32_to_timestr")]];

struct yaffs_obj_hdr{
  yaffs_obj_type type;
  u32 parent_obj_id;
  u16 always_0xFFFF;
  char name[255];
  u8  always_0xFF; /*=0xFF*/
  u16 always_0xFFFF_2;
  u32_file_mode yst_mode;
  u32 yst_uid;
  u32 yst_gid;
  u32_time_t yst_atime;
  u32_time_t yst_mtime;
  u32_time_t yst_ctime;
  u32 file_size_low;
  s32 equiv_id;
  char alias[160];
  u32 yst_rdev;
  u32 win_ctime[2];
  u32 win_atime[2];
  u32 win_mtime[2];
  u32 inband_shadowed_obj_id;
  u32 inband_is_shrink;
  u32 file_size_high;
  u32 reserved[1];
  s32 shadows_obj;
  u32 is_shrink;
};

struct yaffs_spare {
	u8 tb0;
	u8 tb1;
	u8 tb2;
	u8 tb3;
	u8 page_status;		/* set to 0 to delete the chunk */
	u8 block_status;
	u8 tb4;
	u8 tb5;
	u8 ecc1[3];
	u8 tb6;
	u8 tb7;
	u8 ecc2[3];
};

struct yaffs_page_t{
  yaffs_obj_hdr hdr;
  yaffs_spare spare;
};

std::assert(sizeof(yaffs_obj_hdr) == 512, "zeof(yaffs_obj_hdr)==512");

struct yaffs_obj{
  yaffs_obj_hdr hdr;
  yaffs_spare spare;
  if(hdr.type == yaffs_obj_type::YAFFS_OBJECT_TYPE_FILE){
      u8 data[512];
      yaffs_spare data_spare;    
  }
};

std::print(u32_to_timestr(0x65B983eF));



yaffs_obj yaffs_obj_at_0x00[11] @ 0x00;