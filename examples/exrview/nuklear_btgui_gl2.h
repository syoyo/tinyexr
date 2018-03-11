/*
 * Nuklear - v1.00 - public domain
 * no warrenty implied; use at your own risk.
 * authored from 2015-2016 by Micha Mettke
 */
/*
 * ==============================================================
 *
 *                              API
 *
 * ===============================================================
 */
#ifndef NK_BTGUI_GL2_H_
#define NK_BTGUI_GL2_H_

enum nk_btgui_init_state{
    NK_BTGUI3_DEFAULT = 0,
    NK_BTGUI3_INSTALL_CALLBACKS
};

struct nk_btgui_vertex {
    float position[2];
    float uv[2];
    nk_byte col[4];
};

NK_API struct nk_context*   nk_btgui_init(b3gDefaultOpenGLWindow *win, enum nk_btgui_init_state);
NK_API void                 nk_btgui_font_stash_begin(struct nk_font_atlas **atlas);
NK_API void                 nk_btgui_font_stash_end(void);

NK_API void                 nk_btgui_update_mouse_pos(int x, int y);
NK_API void                 nk_btgui_update_mouse_state(int left_button_state, int middle_button_state, int right_button_state);

NK_API void                 nk_btgui_new_frame(void);
NK_API void                 nk_btgui_render(enum nk_anti_aliasing , int max_vertex_buffer, int max_element_buffer);
NK_API void                 nk_btgui_shutdown(void);

NK_API void                 nk_btgui_char_callback(b3gDefaultOpenGLWindow *win, unsigned int codepoint);
NK_API void                 nk_btgui_scroll_callback(b3gDefaultOpenGLWindow *win, double xoff, double yoff);

#endif

/*
 * ==============================================================
 *
 *                          IMPLEMENTATION
 *
 * ===============================================================
 */
#ifdef NK_BTGUI_GL2_IMPLEMENTATION

#ifndef NK_BTGUI_TEXT_MAX
#define NK_BTGUI_TEXT_MAX 256
#endif

struct nk_btgui_device {
    struct nk_buffer cmds;
    struct nk_draw_null_texture null;
    GLuint font_tex;
};

static struct nk_btgui {
    b3gDefaultOpenGLWindow *win;
    int width, height;
    int display_width, display_height;
    struct nk_btgui_device ogl;
    struct nk_context ctx;
    struct nk_font_atlas atlas;
    struct nk_vec2 fb_scale;
    unsigned int text[NK_BTGUI_TEXT_MAX];
    int text_len;
    float scroll;
  
    int left_button_state;
    int middle_button_state;
    int right_button_state;

    int mouse_pos[2];
} btgui;

NK_INTERN void
nk_btgui_device_upload_atlas(const void *image, int width, int height)
{
    struct nk_btgui_device *dev = &btgui.ogl;
    glGenTextures(1, &dev->font_tex);
    glBindTexture(GL_TEXTURE_2D, dev->font_tex);
    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_LINEAR);
    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_LINEAR);
    glTexImage2D(GL_TEXTURE_2D, 0, GL_RGBA, (GLsizei)width, (GLsizei)height, 0,
                GL_RGBA, GL_UNSIGNED_BYTE, image);
    assert(glGetError() == GL_NO_ERROR);
}

NK_API void
nk_btgui_update_mouse_state(int left_button_state, int middle_button_state, int right_button_state)
{
    btgui.left_button_state = left_button_state;
    btgui.middle_button_state = middle_button_state;
    btgui.right_button_state = right_button_state;
}

NK_API void
nk_btgui_update_mouse_pos(int x, int y)
{
    btgui.mouse_pos[0] = x;
    btgui.mouse_pos[1] = y;
}


NK_API void
nk_btgui_render(enum nk_anti_aliasing AA, int max_vertex_buffer, int max_element_buffer)
{
    /* setup global state */
    struct nk_btgui_device *dev = &btgui.ogl;
    glPushAttrib(GL_ENABLE_BIT|GL_COLOR_BUFFER_BIT|GL_TRANSFORM_BIT);
    assert(glGetError() == GL_NO_ERROR);
    glDisable(GL_CULL_FACE);
    glDisable(GL_DEPTH_TEST);
    glEnable(GL_SCISSOR_TEST);
    glEnable(GL_BLEND);
    glEnable(GL_TEXTURE_2D);
    glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);

    /* setup viewport/project */
    glViewport(0,0,(GLsizei)btgui.display_width,(GLsizei)btgui.display_height);
    glMatrixMode(GL_PROJECTION);
    glPushMatrix();
    glLoadIdentity();
    glOrtho(0.0f, btgui.width, btgui.height, 0.0f, -1.0f, 1.0f);
    glMatrixMode(GL_MODELVIEW);
    glPushMatrix();
    glLoadIdentity();

    glEnableClientState(GL_VERTEX_ARRAY);
    glEnableClientState(GL_TEXTURE_COORD_ARRAY);
    glEnableClientState(GL_COLOR_ARRAY);
    {
        GLsizei vs = sizeof(struct nk_btgui_vertex);
        size_t vp = offsetof(struct nk_btgui_vertex, position);
        size_t vt = offsetof(struct nk_btgui_vertex, uv);
        size_t vc = offsetof(struct nk_btgui_vertex, col);

        /* convert from command queue into draw list and draw to screen */
        const struct nk_draw_command *cmd;
        const nk_draw_index *offset = NULL;
        struct nk_buffer vbuf, ebuf;

        /* fill converting configuration */
        struct nk_convert_config config;
        static const struct nk_draw_vertex_layout_element vertex_layout[] = {
            {NK_VERTEX_POSITION, NK_FORMAT_FLOAT, NK_OFFSETOF(struct nk_btgui_vertex, position)},
            {NK_VERTEX_TEXCOORD, NK_FORMAT_FLOAT, NK_OFFSETOF(struct nk_btgui_vertex, uv)},
            {NK_VERTEX_COLOR, NK_FORMAT_R8G8B8A8, NK_OFFSETOF(struct nk_btgui_vertex, col)},
            {NK_VERTEX_LAYOUT_END}
        };
        NK_MEMSET(&config, 0, sizeof(config));
        config.vertex_layout = vertex_layout;
        config.vertex_size = sizeof(struct nk_btgui_vertex);
        config.vertex_alignment = NK_ALIGNOF(struct nk_btgui_vertex);
        config.null = dev->null;
        config.circle_segment_count = 22;
        config.curve_segment_count = 22;
        config.arc_segment_count = 22;
        config.global_alpha = 1.0f;
        config.shape_AA = AA;
        config.line_AA = AA;


        /* convert shapes into vertexes */
        nk_buffer_init_default(&vbuf);
        nk_buffer_init_default(&ebuf);
        nk_convert(&btgui.ctx, &dev->cmds, &vbuf, &ebuf, &config);

        /* setup vertex buffer pointer */
        {const void *vertices = nk_buffer_memory_const(&vbuf);
        glVertexPointer(2, GL_FLOAT, vs, (const void*)((const nk_byte*)vertices + vp));
        glTexCoordPointer(2, GL_FLOAT, vs, (const void*)((const nk_byte*)vertices + vt));
        glColorPointer(4, GL_UNSIGNED_BYTE, vs, (const void*)((const nk_byte*)vertices + vc));}

        /* iterate over and execute each draw command */
        offset = (const nk_draw_index*)nk_buffer_memory_const(&ebuf);
        nk_draw_foreach(cmd, &btgui.ctx, &dev->cmds)
        {
            if (!cmd->elem_count) continue;
            glBindTexture(GL_TEXTURE_2D, (GLuint)cmd->texture.id);
            glScissor(
                (GLint)(cmd->clip_rect.x * btgui.fb_scale.x),
                (GLint)((btgui.height - (GLint)(cmd->clip_rect.y + cmd->clip_rect.h)) * btgui.fb_scale.y),
                (GLint)(cmd->clip_rect.w * btgui.fb_scale.x),
                (GLint)(cmd->clip_rect.h * btgui.fb_scale.y));
            glDrawElements(GL_TRIANGLES, (GLsizei)cmd->elem_count, GL_UNSIGNED_SHORT, offset);
            offset += cmd->elem_count;
        }
        nk_clear(&btgui.ctx);
        nk_buffer_free(&vbuf);
        nk_buffer_free(&ebuf);
    }
    assert(glGetError() == GL_NO_ERROR);

    /* default OpenGL state */
    glDisableClientState(GL_VERTEX_ARRAY);
    glDisableClientState(GL_TEXTURE_COORD_ARRAY);
    glDisableClientState(GL_COLOR_ARRAY);
    assert(glGetError() == GL_NO_ERROR);

    glDisable(GL_CULL_FACE);
    glDisable(GL_DEPTH_TEST);
    glDisable(GL_SCISSOR_TEST);
    glDisable(GL_BLEND);
    glDisable(GL_TEXTURE_2D);

    glBindTexture(GL_TEXTURE_2D, 0);
    glMatrixMode(GL_MODELVIEW);
    glPopMatrix();
    glMatrixMode(GL_PROJECTION);
    glPopMatrix();
    glPopAttrib();
    assert(glGetError() == GL_NO_ERROR);
}

#if 0 // @todo
NK_API void
nk_btgui_char_callback(b3gDefaultOpenGLWindow *win, unsigned int codepoint)
{
    (void)win;
    if (btgui.text_len < NK_BTGUI_TEXT_MAX)
        btgui.text[btgui.text_len++] = codepoint;
}

NK_API void
nk_gflw3_scroll_callback(b3gDefaultOpenGLWindow *win, double xoff, double yoff)
{
    (void)win; (void)xoff;
    btgui.scroll += (float)yoff;
}

static void
nk_btgui_clipbard_paste(nk_handle usr, struct nk_text_edit *edit)
{
    const char *text = btguiGetClipboardString(btgui.win);
    if (text) nk_textedit_paste(edit, text, nk_strlen(text));
    (void)usr;
}

static void
nk_btgui_clipbard_copy(nk_handle usr, const char *text, int len)
{
    char *str = 0;
    (void)usr;
    if (!len) return;
    str = (char*)malloc((size_t)len+1);
    if (!str) return;
    memcpy(str, text, (size_t)len);
    str[len] = '\0';
    btguiSetClipboardString(btgui.win, str);
    free(str);
}
#endif

NK_API struct nk_context*
nk_btgui_init(b3gDefaultOpenGLWindow *win, enum nk_btgui_init_state init_state)
{
    btgui.win = win;
    if (init_state == NK_BTGUI3_INSTALL_CALLBACKS) {
        //btguiSetScrollCallback(win, nk_gflw3_scroll_callback);
        //btguiSetCharCallback(win, nk_btgui_char_callback);
    }

    nk_init_default(&btgui.ctx, 0);
    //btgui.ctx.clip.copy = nk_btgui_clipbard_copy;
    //btgui.ctx.clip.paste = nk_btgui_clipbard_paste;
    //btgui.ctx.clip.userdata = nk_handle_ptr(0);
    nk_buffer_init_default(&btgui.ogl.cmds);
    return &btgui.ctx;
}

NK_API void
nk_btgui_font_stash_begin(struct nk_font_atlas **atlas)
{
    nk_font_atlas_init_default(&btgui.atlas);
    nk_font_atlas_begin(&btgui.atlas);
    *atlas = &btgui.atlas;
}

NK_API void
nk_btgui_font_stash_end(void)
{
    const void *image; int w, h;
    image = nk_font_atlas_bake(&btgui.atlas, &w, &h, NK_FONT_ATLAS_RGBA32);
    nk_btgui_device_upload_atlas(image, w, h);
    nk_font_atlas_end(&btgui.atlas, nk_handle_id((int)btgui.ogl.font_tex), &btgui.ogl.null);
    if (btgui.atlas.default_font)
        nk_style_set_font(&btgui.ctx, &btgui.atlas.default_font->handle);
}

NK_API void
nk_btgui_new_frame(void)
{
    int i;
    //double x, y;
    struct nk_context *ctx = &btgui.ctx;
    b3gDefaultOpenGLWindow *win = btgui.win;

    btgui.width = win->getWidth();
    btgui.height = win->getHeight();

    float fbscale = 1.0;
#ifdef __APPLE__
    //fbscale = win->getRetinaScale();
#endif
    btgui.display_width  = fbscale * btgui.width;
    btgui.display_height = fbscale * btgui.height;

    btgui.fb_scale.x = (float)btgui.display_width/(float)btgui.width;
    btgui.fb_scale.y = (float)btgui.display_height/(float)btgui.height;

    // HACK
    btgui.fb_scale.x = 1.0;
    btgui.fb_scale.y = 1.0;


    nk_input_begin(ctx);
#if 0
    for (i = 0; i < btgui.text_len; ++i)
        nk_input_unicode(ctx, btgui.text[i]);

    nk_input_key(ctx, NK_KEY_DEL, btguiGetKey(win, BTGUI_KEY_DELETE) == BTGUI_PRESS);
    nk_input_key(ctx, NK_KEY_ENTER, btguiGetKey(win, BTGUI_KEY_ENTER) == BTGUI_PRESS);
    nk_input_key(ctx, NK_KEY_TAB, btguiGetKey(win, BTGUI_KEY_TAB) == BTGUI_PRESS);
    nk_input_key(ctx, NK_KEY_BACKSPACE, btguiGetKey(win, BTGUI_KEY_BACKSPACE) == BTGUI_PRESS);
    nk_input_key(ctx, NK_KEY_UP, btguiGetKey(win, BTGUI_KEY_UP) == BTGUI_PRESS);
    nk_input_key(ctx, NK_KEY_DOWN, btguiGetKey(win, BTGUI_KEY_DOWN) == BTGUI_PRESS);
    nk_input_key(ctx, NK_KEY_TEXT_START, btguiGetKey(win, BTGUI_KEY_HOME) == BTGUI_PRESS);
    nk_input_key(ctx, NK_KEY_TEXT_END, btguiGetKey(win, BTGUI_KEY_END) == BTGUI_PRESS);
    nk_input_key(ctx, NK_KEY_SHIFT, btguiGetKey(win, BTGUI_KEY_LEFT_SHIFT) == BTGUI_PRESS||
                                    btguiGetKey(win, BTGUI_KEY_RIGHT_SHIFT) == BTGUI_PRESS);

    if (btguiGetKey(win, BTGUI_KEY_LEFT_CONTROL) == BTGUI_PRESS ||
        btguiGetKey(win, BTGUI_KEY_RIGHT_CONTROL)) {
        nk_input_key(ctx, NK_KEY_COPY, btguiGetKey(win, BTGUI_KEY_C) == BTGUI_PRESS);
        nk_input_key(ctx, NK_KEY_PASTE, btguiGetKey(win, BTGUI_KEY_P) == BTGUI_PRESS);
        nk_input_key(ctx, NK_KEY_CUT, btguiGetKey(win, BTGUI_KEY_X) == BTGUI_PRESS);
        nk_input_key(ctx, NK_KEY_TEXT_UNDO, btguiGetKey(win, BTGUI_KEY_Z) == BTGUI_PRESS);
        nk_input_key(ctx, NK_KEY_TEXT_REDO, btguiGetKey(win, BTGUI_KEY_R) == BTGUI_PRESS);
        nk_input_key(ctx, NK_KEY_TEXT_WORD_LEFT, btguiGetKey(win, BTGUI_KEY_LEFT) == BTGUI_PRESS);
        nk_input_key(ctx, NK_KEY_TEXT_WORD_RIGHT, btguiGetKey(win, BTGUI_KEY_RIGHT) == BTGUI_PRESS);
        nk_input_key(ctx, NK_KEY_TEXT_LINE_START, btguiGetKey(win, BTGUI_KEY_B) == BTGUI_PRESS);
        nk_input_key(ctx, NK_KEY_TEXT_LINE_END, btguiGetKey(win, BTGUI_KEY_E) == BTGUI_PRESS);
    } else {
        nk_input_key(ctx, NK_KEY_LEFT, btguiGetKey(win, BTGUI_KEY_LEFT) == BTGUI_PRESS);
        nk_input_key(ctx, NK_KEY_RIGHT, btguiGetKey(win, BTGUI_KEY_RIGHT) == BTGUI_PRESS);
        nk_input_key(ctx, NK_KEY_COPY, 0);
        nk_input_key(ctx, NK_KEY_PASTE, 0);
        nk_input_key(ctx, NK_KEY_CUT, 0);
        nk_input_key(ctx, NK_KEY_SHIFT, 0);
    }

    btguiGetCursorPos(win, &x, &y);
    nk_input_motion(ctx, (int)x, (int)y);
    nk_input_button(ctx, NK_BUTTON_LEFT, (int)x, (int)y, btguiGetMouseButton(win, BTGUI_MOUSE_BUTTON_LEFT) == BTGUI_PRESS);
    nk_input_button(ctx, NK_BUTTON_MIDDLE, (int)x, (int)y, btguiGetMouseButton(win, BTGUI_MOUSE_BUTTON_MIDDLE) == BTGUI_PRESS);
    nk_input_button(ctx, NK_BUTTON_RIGHT, (int)x, (int)y, btguiGetMouseButton(win, BTGUI_MOUSE_BUTTON_RIGHT) == BTGUI_PRESS);
    nk_input_scroll(ctx, btgui.scroll);
#endif
    nk_input_motion(ctx, btgui.mouse_pos[0], btgui.mouse_pos[1]);
    nk_input_button(ctx, NK_BUTTON_LEFT,   btgui.mouse_pos[0], btgui.mouse_pos[1], btgui.left_button_state);
    nk_input_button(ctx, NK_BUTTON_MIDDLE, btgui.mouse_pos[0], btgui.mouse_pos[1], btgui.middle_button_state);
    nk_input_button(ctx, NK_BUTTON_RIGHT,  btgui.mouse_pos[0], btgui.mouse_pos[1], btgui.right_button_state);
    nk_input_end(&btgui.ctx);
    btgui.text_len = 0;
    btgui.scroll = 0;
}

NK_API
void nk_btgui_shutdown(void)
{
    struct nk_btgui_device *dev = &btgui.ogl;
    nk_font_atlas_clear(&btgui.atlas);
    nk_free(&btgui.ctx);
    glDeleteTextures(1, &dev->font_tex);
    nk_buffer_free(&dev->cmds);
    memset(&btgui, 0, sizeof(btgui));
}

#endif

