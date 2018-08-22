using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.Windows.Forms;

namespace FsMiniMAL.PrinterTest
{
    public partial class Form1 : Form
    {
        public Form1()
        {
            InitializeComponent();
        }

        protected override void OnSizeChanged(EventArgs e)
        {
            base.OnSizeChanged(e);
            this.Invalidate();
        }

        protected override void OnPaint(PaintEventArgs e)
        {
            base.OnPaint(e);

            var g = this.CreateGraphics();
            g.Clear(Color.White);
            var fontSize = 20.0f;
            var font = new Font("Consolas", fontSize, GraphicsUnit.Pixel);
            var w = (int)Math.Round(g.MeasureString("a", font, new PointF(), StringFormat.GenericTypographic).Width);
            var cols = (int)(this.Width / w) - 5;
            g.FillRectangle(Brushes.LightGray, 0f, 0f, cols * w, this.Height);
            var interp = FsMiniMAL.Top.createInterpreter();
            //i.Do("array_init 100 (fn n -> n * n)");
            //interp.Do("array_init 30 (fn n -> array_init 5 (fn m -> begin val n = n + 1; val m = m + 1; var accu = 1; for u = 0 to m - 1 do accu <- accu * n; accu end))");
            //interp.Do("[|[|[|[|1,2,3|],[|4,5,6|]|]|]|]");
            interp.Do("(100000, 1000000, -100000000, Some (-1000000000, 100000))");
            var (tyenv, val, ty) = interp.Result;
            var (s, levels) = Printer.print_value2(tyenv, cols, ty, val);
            g.DrawString(cols.ToString(), font, Brushes.Black, new PointF(0f, 0f), StringFormat.GenericTypographic);

            var brushes = new[]
            {
                Brushes.LightGreen,
                Brushes.LightPink,
                Brushes.LightCyan,
                Brushes.LightYellow,
                Brushes.LightBlue,
                Brushes.LightSalmon,
                Brushes.LightCoral
            };

            var x = 0f;
            var y = 22f;
            var i = 0;
            while (i < s.Length)
            {
                var c = s[i];
                if (c == '\r' || c == '\n')
                {
                    x = 0f;
                    y += 22f;
                    if (i + 1 < s.Length && s[i + 1] == '\n') i++;
                }
                else
                {
                    var level = levels[i];
                    g.FillRectangle(brushes[level < 0 ? ~level : level], new RectangleF(x, y, w, 22f));
                    if (level < 0)
                    {
                        g.FillRectangle(Brushes.Red, new RectangleF(x, y + 20f, w, 2f));
                    }
                    g.DrawString(new String(c, 1), font, Brushes.Black, new PointF(x, y), StringFormat.GenericTypographic);
                    x += w;
                }

                i++;
            }

            // g.DrawString(s, font, Brushes.Black, new PointF(0f, 20f), StringFormat.GenericTypographic);
        }
    }
}
