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
            var fontSize = 16.0f;
            var font = new Font("Consolas", fontSize);
            var w = g.MeasureString("a", font, new PointF(), StringFormat.GenericTypographic).Width;
            var cols = (int)(this.Width / w) - 5;
            g.FillRectangle(Brushes.LightGray, 0f, 0f, cols * w, this.Height);
            var i = new FsMiniMAL.Interpreter();
            //i.Do("array_init 100 (fn n -> n * n)");
            i.Do("array_init 30 (fn n -> array_init 5 (fn m -> begin val n = n + 1; val m = m + 1; var accu = 1; for u = 0 to m - 1 do accu <- accu * n; accu end))");
            var val = i.Result.Item1;
            var ty = i.Result.Item2;
            var s = FsMiniMAL.Printer.print_value_without_type(i.TypeEnv, cols, ty, val);
            g.DrawString(cols.ToString() + "\r\n" + s, font, Brushes.Black, new PointF(), StringFormat.GenericTypographic);
        }
    }
}
