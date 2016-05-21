varying vec2 texcoord;

uniform sampler2D tex;

void main()
{
	vec4 rgba = texture2D(tex, texcoord);
	gl_FragColor = vec4(rgba.rgb, 1.0);
}
